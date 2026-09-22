# 递归关系观察：算术编码与有效分辨率

本卷研究同一对象在同余、数码、回返块、前缀及概率表示之间的运输，承接[运输、任务记忆与完成化卷](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)的实际续接接口。完整档案 $C$ 及合法操作不会因编码而被删除。可表达、可识别、可取得、可认证、可计算归一化与共同实现分别给出条件。

第1章连接有限算术、继续复杂度与回返块。第2章依次讨论有效提升、唯一固定的三进对角集合、质量局部化、有限认证、规范柱、奇进及二进边界、变量进制和条件采样；回返块所引用的常数进制结论在变量进制部分独立证明。第3章限定有限一致性、HALT、自模拟及理论相对独立性的逻辑阈值。

以下是普通数学推导和所列版本范围内的既有结果应用，不是新增 Lean 核验，也不因综合而主张原创。式号 TM 保留跨卷唯一地址。非均匀 Perron 权下的稀疏质量—延拓分类仍须另证；均匀块概率不能替换原有概率模型。

## 1. 有限算术、数码续接与回返块

### 1.1 素数分辨率、共同剩余与约束闭合

有限同余覆盖中，增加模数分辨率与排除候选是两个不同动作。下述计数明确分开这两个动作，并给出有限覆盖最后一步、不可冗余覆盖及无限完成化的适用边界。它们是由整数同余与有限 CRT 直接得到的普通数学结果，不作为 Erdős 第 7 问的解答或原创性声明。

#### 1.1.1 同一旧状态的精确提升数

设 $L,m$ 为正整数，旧幸存集合为
$H\subseteq\mathbb Z/L\mathbb Z$，新增要排除的同余类为
$a+m\mathbb Z$，其中 $a\in\mathbb Z$。置
$$
d=\gcd(L,m),\qquad
L'=\operatorname{lcm}(L,m),\qquad
k=\frac md=\frac{L'}L .
\tag{TM.352}
$$
以自然剩余映射 $\pi_{L',L}$ 将新分辨率投回旧分辨率，新幸存集合为
$$
H'=\{x\in\mathbb Z/L'\mathbb Z:
       \pi_{L',L}(x)\in H,\quad x\not\equiv a\pmod m\}.
\tag{TM.353}
$$
若 $h\in\mathbb Z/L\mathbb Z$，取整数代表 $h_0$。其在模 $L'$ 中的提升恰为
$h_0+jL$，$0\le j<k$，共有 $k$ 个。不同 $j$ 给不同剩余类，因为 $L'=kL$。

该纤维中被新同余类删去的点，满足
$h_0+jL\equiv a\pmod m$。它有解当且仅当
$h_0\equiv a\pmod d$；满足此条件时，约去 $d$ 后得到
$(L/d)j\equiv(a-h_0)/d\pmod{k}$。
由于 $\gcd(L/d,k)=1$，解在模 $k$ 下唯一。因此
$$
\#\{x:\pi_{L',L}(x)=h,\ x\equiv a\pmod m\} =
\begin{cases}
1,&h\equiv a\pmod d,\\
0,&h\not\equiv a\pmod d.
\end{cases}
\tag{TM.354}
$$
这里 $h\bmod d$ 定义良好，因为 $d\mid L$。整个计数属于同一个模 $L'$ 的共同实现，未把模 $L$ 与模 $m$ 的自由乘积当作实际联合像。

#### 1.1.2 精确递推与两个变化方向

定义共同 gcd 切面的剩余量
$$
R_d(a;H)=\#\{h\in H:h\equiv a\pmod d\}.
$$
逐个旧纤维相加，得到精确递推
$$
|H'|=k|H|-R_d(a;H),\qquad
0\le R_d(a;H)\le |H|.
\tag{TM.355}
$$
特别地，
$$
|H'|\ge(k-1)|H|.
\tag{TM.356}
$$
若 $k>1$ 且 $H\ne\varnothing$，新幸存集合必非空。若全部模数为奇数，则 $k$ 也是奇数，$k>1$ 时必有 $k\ge3$，故幸存代表数至少翻倍。

这里增长的是更大有限商中的代表数。令
$\delta=|H|/L$、$\delta'=|H'|/L'$，则
$$
\delta'=\delta-\frac{R_d(a;H)}{L'}\le\delta.
\tag{TM.357}
$$
因此幸存代表数增加与幸存密度下降可以同时发生，不能把二者混称为同一种信息增长。又
$R_d(a;H)\le L/d$，故一次删除的密度不超过 $1/m$，与新增同余类的整体密度一致。

模数分辨率的对数增量为
$$
\log L'-\log L
=\log k
=\sum_p\max\{0,v_p(m)-v_p(L)\}\log p.
\tag{TM.358}
$$
式（TM.358）只统计哪些素数方向增加了精度。它本身既不是对任意实际概率律的 Shannon 信息，也没有统计新增类删掉了哪些旧候选。相容约束通过式（TM.355）的 $R_d(a;H)$ 承担另一项作用。

#### 1.1.3 首次有限覆盖的最后一步没有分辨率增量

假设旧集合 $H\ne\varnothing$。由
$R_d(a;H)\le |H|$ 和 $k\ge1$，有
$$
H'=\varnothing
\iff
\left[
m\mid L
\quad\text{且}\quad
H\subseteq\{h:h\equiv a\pmod m\}
\right].
\tag{TM.359}
$$
证明：若 $H'$ 为空，式（TM.355）给
$k|H|=R_d(a;H)\le|H|$，故 $k=1$，也就是 $m\mid L$；
此时 $d=m$、$L'=L$，而 $R_m(a;H)=|H|$ 恰好表示全部旧幸存者属于新类。反向由定义立即成立。

给定有限有序同余类
$(a_1\bmod m_1),\ldots,(a_N\bmod m_N)$，从
$L_0=1$、$H_0=\mathbb Z/\mathbb Z$ 开始，置
$L_j=\operatorname{lcm}(m_1,\ldots,m_j)$，令 $H_j$ 为前 $j$ 个类尚未覆盖的模 $L_j$ 剩余。若每一步均严格增加 LCM，则
$$
L_j>L_{j-1}\ \ (1\le j\le N)
\quad\Longrightarrow\quad
H_j\ne\varnothing\ \ (0\le j\le N).
\tag{TM.360}
$$
这是从式（TM.356）出发的有限归纳。若模数全奇，则还得到
$|H_j|\ge2^j$，但式（TM.357）仍允许密度下降。

因此，任何首次完成覆盖的最后一步必有
$L_N=L_{N-1}$，即该步只增加约束而不增加模数分辨率。此结论需要“此前尚未覆盖”的前提；已有覆盖后追加一个新模数当然可以增加 LCM，追加类只是冗余的。

由此，删去或合并全部零分辨率增量层，可能恰好删去使有限覆盖闭合的步骤。模数互不相同并不意味着 LCM 每步严格增长，例如先出现模 $9$、后出现模 $3$，后一步就是新模数而非新分辨率。

#### 1.1.4 不可冗余有限覆盖的最大素数幂必须重复出现

称一个有限覆盖不可冗余，指删除其中任意一个同余类后，都不再覆盖全部整数。设其模数为
$m_1,\ldots,m_N>0$。固定任意 $i$，把第 $i$ 个类排在最后；此前因为不可冗余性仍有幸存者，而加入它之后首次完成覆盖。式（TM.359）给
$$
m_i\mid \operatorname{lcm}_{j\ne i}m_j
\qquad(1\le i\le N).
\tag{TM.361}
$$
空集合的 LCM 按一处理；单个模一的平凡覆盖也符合该式。

对任意出现过的素数 $p$，令
$E_p=\max_jv_p(m_j)>0$。若只有一个 $m_i$ 达到该最大指数，式（TM.361）就会失败。因此
$$
\#\{i:v_p(m_i)=E_p\}\ge2
\qquad(E_p>0).
\tag{TM.362}
$$
这是最高素数幂的重复，不是整个模数的重复。不同模数完全可以具有相同最高素数幂；例如 $15,21,35$ 的每个出现素数都达到两次最高指数。这个模数列表仅说明两种“重复”的区别，不是覆盖实例。

更一般地，在任意有限覆盖中，如果某个模数不整除其余模数的 LCM，那么删除该同余类后仍然覆盖；否则把它排在最后会违反式（TM.359）。因此某个素数最高指数的唯一承担者必对应冗余类。

这些条件都是必要条件。它们既不提供充分的覆盖构造，也不推出所有互异奇数模数族都会具有唯一最高素数幂。不能以它们取代完整覆盖问题。

#### 1.1.5 一个标量不是可递推的幸存状态

只保存分辨率 $\log L$、幸存数 $|H|$ 及已用模数集合，仍不足以决定下一步会删掉多少候选。对每个 $d\mid L$，定义实际共同分布轮廓
$$
K_d(a;H)=\#\{h\in H:h\equiv a\pmod d\}.
\tag{TM.363}
$$
给定新增类 $a\bmod m$，式（TM.355）需要的正是
$K_{\gcd(L,m)}(a;H)$，不能用总数替代。

下面两份前缀都满足模数为互异奇数且大于一的限制：

| 旧前缀 | $L$ | $|H|$ | 已用模数 | 同样新增 $0\bmod3$ 后 |
|---|---:|---:|---|---:|
| 仅 $0\bmod9$ | 9 | 8 | $\{9\}$ | 6 个幸存者 |
| 仅 $1\bmod9$ | 9 | 8 | $\{9\}$ | 5 个幸存者 |

第一份的旧幸存者中，模三为零的只有 $3,6$，第二份则有
$0,3,6$。两份都满足 $d=3,k=1$，所以
$$
8-K_3(0;H_{\rm first})=8-2=6,\qquad
8-K_3(0;H_{\rm second})=8-3=5.
\tag{TM.364}
$$
这是两个明确共同实现上的一阶递推反例：相同的三个粗摘要，对同一合法新动作产生不同后继幸存数。它没有假设任何全局覆盖存在。

对于完整的确定性递推，$(L,H,U)$ 是一个充分状态，其中 $U$ 保存已用模数，以决定“模数须互异”的动作合法性；后继 $L',H',U\cup\{m\}$ 由式（TM.352）—（TM.353）确定。寻找更小摘要时，需要证明其既能恢复相应 $K_d$，又能继续更新所有未来所需的轮廓。仅保存几个互不相连的边缘计数不自动满足这种动态闭合。若保存所有 $d\mid L$ 的完整轮廓，则 $K_L$ 已经恢复整个 $H$，不能把该全集轮廓称作已经取得压缩。

因此这里的 DP 任务是保留足够的共同剩余关系，而不是仅让一个信息标量随步骤增长。

#### 1.1.6 有限覆盖在整数与 profinite 完成对象上等价

对任意固定有限同余族，令 $L$ 为全部模数的 LCM、$H$ 为其模 $L$ 幸存集合。每个剩余类都有整数代表，各覆盖条件都只依赖模 $L$ 读数。因此
$$
\begin{aligned}
\text{该有限族覆盖 }\mathbb Z
&\iff H=\varnothing\\
&\iff\text{该有限族的柱集覆盖 }\widehat{\mathbb Z}.
\end{aligned}
\tag{TM.365}
$$
最后一步使用 profinite 整数的模 $L$ 映射满射；若 $H\ne\varnothing$，其整数代表同时见证整数不覆盖，也给出 profinite 不覆盖。反过来任何 profinite 幸存点的模 $L$ 读数，也由一个普通整数实现全部这些有限条件。

等价性的关键是条件族固定有限。它不允许把任意无限相容幸存线程直接当作普通整数。

#### 1.1.7 全部整数被可数覆盖，完成对象仍有正测度幸存

枚举整数为 $z_1,z_2,\ldots$，每个整数至少出现一次。对 $n\ge1$ 定义
$$
C_n=\{x\in\widehat{\mathbb Z}:
       x\equiv z_n\pmod{3^n}\}
=z_n+3^n\widehat{\mathbb Z}.
\tag{TM.366}
$$
模数 $3^n$ 全部互异、为大于一的奇数，前 $n$ 项的
LCM 恰为 $3^n$，所以每步严格增加分辨率。

令 $\mu$ 为 $\widehat{\mathbb Z}$ 的归一化 Haar 概率测度。
模 $3^n$ 的 $3^n$ 个纤维互为平移并构成分划，因此
$$
\mu(C_n)=3^{-n},\qquad
\mu\!\left(\bigcup_{n\ge1}C_n\right)
\le\sum_{n\ge1}3^{-n}=\frac12.
\tag{TM.367}
$$
故
$$
K_{\mathrm{int}}=\widehat{\mathbb Z}\setminus\bigcup_{n\ge1}C_n
\quad\text{满足}\quad
\mu(K_{\mathrm{int}})\ge\frac12,
\qquad K_{\mathrm{int}}\ne\varnothing.
\tag{TM.368}
$$
每个 $C_n$ 开闭，故 $K_{\mathrm{int}}$ 闭且紧。另一方面，每个嵌入的普通整数 $z$ 都等于某个 $z_n$，从而属于 $C_n$。因此
$$
K_{\mathrm{int}}\cap\mathbb Z=\varnothing,
\qquad
\mathbb Z\subseteq\bigcup_{n\ge1}C_n .
\tag{TM.369}
$$
这里把 $\mathbb Z$ 视作它在 $\widehat{\mathbb Z}$ 中的典范嵌入。正测度闭集与全部普通整数不相交不矛盾：整数嵌入虽然稠密，但不是这个紧完成对象的全部点。

每个有限前缀仍有许多幸存者。由有限并的同一测度界，
$$
\frac{|H_N|}{3^N}
\ge1-\sum_{n=1}^N3^{-n}
=\frac{1+3^{-N}}2,
\qquad
|H_N|\ge\frac{3^N+1}{2}.
\tag{TM.370}
$$
这个下界也可直接从提升计数得到：此时旧模数为 $3^{N-1}$，
新模数为 $3^N$，所以 $k=3,d=3^{N-1}$，新类在旧剩余中至多选中一个点。于是 $|H_N|\ge3|H_{N-1}|-1$，从
$|H_0|=1$ 归纳得相同结论。

因此，任意有限阶段都有普通整数幸存者，而所有阶段一起却没有普通整数幸存者；全体阶段的相容幸存实现位于完成对象中。这个例子保留式（TM.365）的全部有限等价性，揭示的是无限量词下必须声明全局实现的载体。

此构造为可数无限覆盖，不是有限互异奇数模数覆盖。它不解决有限 Erdős 第 7 问，也不把“每步严格增加 LCM”有限归纳成“存在一个普通整数永远幸存”。

已发布的 docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md 的外部章节9（提交 0b499abf718df8517cc05b8554d20467389014a4）给出了以全部奇素数为模数、覆盖全部整数而 profinite 幸存集合非空且 Haar 测度为零的版本；本节以单个素数的幂增加精度，保留至少一半的幸存质量，二者共同区分相容实现、普通整数实现与极限质量。

#### 1.1.8 有限抽样能发现幸存者，不能替代空集证书

固定有限模数 $L>1$ 及其真实幸存集合 $H$。独立、均匀地从
$\mathbb Z/L\mathbb Z$ 抽样 $N$ 次，并准确判断每个样本是否属于 $H$。若 $H\ne\varnothing$，一次都没有命中的概率为
$$
\Pr(\text{miss }H)
=\left(1-\frac{|H|}{L}\right)^N
\le\left(1-\frac1L\right)^N .
\tag{TM.371}
$$
对 $0<\alpha<1$，令
$$
N\ge
\left\lceil\frac{\log\alpha}{\log(1-1/L)}\right\rceil
\tag{TM.372}
$$
即可使最坏漏检概率不超过 $\alpha$。若要一个更直观的充分值，
由 $1-u\le e^{-u}$ 得
$$
N\ge\left\lceil L\log(1/\alpha)\right\rceil
\quad\Longrightarrow\quad
\Pr(\text{miss }H)\le\alpha.
\tag{TM.373}
$$
式（TM.372）在 $L\to\infty$ 时的主尺度为
$L\log(1/\alpha)$。若 $L=1$，非空 $H$ 只有唯一一个点，一次抽样即可命中，应单独处理，不代入 $\log(1-1/L)$。

命中一个经验证的幸存样本，是不覆盖的具体证书；有限次数未命中，只是上述漏检概率控制，不是逻辑空集证明，也不是在未指定先验时对 $H=\varnothing$ 的后验概率。非均匀、相关抽样或近似成员判定需要另一份误差模型。

在无限完成对象上，若幸存集合非空但 Haar 测度为零，即使理想化地准许精确成员判定，任意可数次独立 Haar 抽样也几乎必然不命中它。因此随机搜索不能代替一般存在判定。反之，式（TM.368）的正测度例子并不自动赋予有限算法判定某点是否满足全部可数约束的能力。

#### 1.1.9 与既有接口及开放目标的关系

本节直接依赖有限剩余的共同实现、提升和计数。不可变项目快照
9d416050c9a90f785d50f2a5034f1a1f99334d62 中，现有支点包括：

- D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.lean:51，
  joint_residue_image_eq_compatible_pairs：模 $L$ 与模 $m$ 的实际联合像，恰好由模 $\gcd(L,m)$ 上相容的剩余对组成。
- D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt.lean:112，
  finite_crt_gluing：有限非互素同余族的成对 gcd 相容性、普通整数共同实现及模 LCM 的唯一剩余类；不把有限剩余类唯一性误作整数代表唯一性。
- D5/S3/Arith/Covering/CoveringSystem.lean:23，
  IsCoveringSystem 明确覆盖对象为全部整数，允许一般正模数；
  同文件第27行 IsDistinct 额外明确每个模数至少二、且模数两两不同；
  第31行 AllOdd 明确所有模数为奇数；
  第36行 sum_reciprocal_moduli_ge_one 给有限覆盖的倒数模数和必要下界。

因此在本项目的有限互异奇数覆盖目标中，必须同时保留有限族、模数互异、模数大于一、全体整数覆盖这几项条件；仅说“奇数”而允许模一，会引入一类即覆盖全部整数的平凡实例。

上述结果仍允许存在含零 LCM 增量约束层的待研究有限奇数互异模数族。因此本节明确排除了“忽略所有约束层，只看分辨率增长便可判覆盖”的方法，不宣称已经证明或反驳有限覆盖开放命题。

### 1.2 编码分辨率的关系运输：整数值、权重相位与终态约束

Zeckendorf、一般禁止 $1^k$ 的 k-bonacci 编码与普通二进制，可以表示同一批非负整数；这给出完整有限名字之间的可逆转换。然而，完整解码、有限前缀观察、数字移位、终态判定与完成化，是不同的关系任务。本节给出它们能够共同运输的部分，以及固定深度观察不能互换的确切障碍。

本节均为下列定义下的普通数学推导。仓内已有声明的归属在末尾单列；没有把新增推导宣称为已经完成 Lean 核验。

#### 1.2.1 先固定数值任务与编码载体

固定整数 $k\ge2$，定义整数位权
$$
G_j^{(k)}=2^j\quad(0\le j<k),\qquad
G_j^{(k)}=\sum_{h=1}^{k}G_{j-h}^{(k)}\quad(j\ge k).
\tag{TM.374}
$$
固定 $k$ 时省略上标。令 $\mathcal W_N^{(k)}$ 为长度恰好为 $N$、不含连续 $k$ 个一的二进制词。下标 $j=0$ 表示最低位；通常打印的整数词把最高位写在左边。数值定义为
$$
\operatorname{val}_k(b)=\sum_{j=0}^{N-1}b_jG_j.
\tag{TM.375}
$$
这些是整数权重，不是以增长根 $\lambda_k$ 的负幂作权重的实数展开。两种解码器各有用途，不能只因合法词相同而混用。

若目标是同余覆盖，先固定模数 $m>1$、剩余集 $R_m=\mathbb Z/m\mathbb Z$、真实终态覆盖集 $C_m\subseteq R_m$ 与幸存集 $S_m=R_m\setminus C_m$。原始同余条件应先在共同整数源上确定这一任务，再运输到编码；不能沿不同数字分支改动覆盖标签。

#### 1.2.2 一般区间唯一性：合法 N 位词恰好表示一个整数区间

对每个 $N\ge0$，数值映射给出双射
$$
\operatorname{val}_k:\mathcal W_N^{(k)}
\overset{\sim}{\longrightarrow}
\{0,1,\ldots,G_N-1\}.
\tag{TM.376}
$$
证明对 $N$ 作强归纳。$N<k$ 时没有禁词约束，所有所用权重均为二的幂，结论就是固定长度的二进制唯一表示；$N=0$ 时空词唯一表示零，且 $G_0=1$。

设 $N\ge k$。从最高位开始，一个合法词必有唯一的形式 $1^j0v$，其中 $0\le j<k$，而 $v$ 是长度 $N-j-1$ 的合法词。定义
$$
A_0=0,\qquad A_j=\sum_{h=1}^{j}G_{N-h}\quad(1\le j\le k).
\tag{TM.377}
$$
前面的 $j$ 个一贡献数值 $A_j$。由归纳假设，尾词 $v$ 唯一遍历从零到 $G_{N-j-1}-1$ 的整数，故这一组词唯一遍历
$$
[A_j,A_j+G_{N-j-1})\cap\mathbb Z
=[A_j,A_{j+1})\cap\mathbb Z.
\tag{TM.378}
$$
这些区间首尾相接且互不重叠，并且由递推
$$
A_k=\sum_{h=1}^{k}G_{N-h}=G_N.
\tag{TM.379}
$$
因而所有分组恰好无重叠地覆盖目标区间。每组内部的唯一性由归纳假设保证，组间唯一性由区间不交保证，双射得证。

这份证明同时给出编码算法：先确定目标整数落在哪个区间，输出相应的高位串 $1^j0$，减去 $A_j$ 后递归编码尾部。仅证明合法词数为 $G_N$，尚不足以证明某个指定数值映射是双射；上述区间分解补足了这一点。

#### 1.2.3 规范表示、前导零与模余数编码

固定长度表示允许最高位一侧补零。对正整数去掉这些前导零，并约定零的规范表示为空词。位权严格增长且无界：初始段严格增长；对 $j\ge k$，递推包含 $G_{j-1}$ 及至少一个正项，所以 $G_j>G_{j-1}$。于是每个自然数都落入某个式（TM.376）的区间。

不同长度的唯一性也成立：若两个词表示同一整数，先在较短词的最高位一侧补零到相同长度，再使用式（TM.376）。因此得到规范编码双射
$$
\operatorname{enc}_k:\mathbb N\overset{\sim}{\longrightarrow}\mathcal C_k.
\tag{TM.380}
$$
$k=2$ 时位权为 $1,2,3,5,\ldots$，即这里采用的 Zeckendorf 编码；$k=3$ 时为 $1,2,4,7,\ldots$。$k=1$ 不在本节范围内：禁止单个一会只留下全零词。

对 $R_m$，须先选标准代表元 $\operatorname{rep}_m(r)\in\{0,\ldots,m-1\}$，再定义
$$
E_{k,m}(r)=\operatorname{enc}_k(\operatorname{rep}_m(r)),\qquad
\mathcal C_{k,m}=E_{k,m}(R_m).
\tag{TM.381}
$$
$E_{k,m}$ 是到实际代码集 $\mathcal C_{k,m}$ 的双射。可以给所有词一致补零到足够长度；但数值大于等于 $m$ 的其他合法词不是新的剩余类，只是模约化后的冗余代表。后续的代码集基数与概率运输均针对这个明确选定的代码集。

#### 1.2.4 精确容量界与固定 k 下的长度标度

存在唯一 $\lambda_k\in(1,2)$ 满足
$$
\sum_{h=1}^{k}\lambda_k^{-h}=1,
\qquad
\lambda_k^k=\lambda_k^{k-1}+\cdots+1.
\tag{TM.382}
$$
存在唯一性来自倒数幂和的连续严格递减：它在一处等于 $k>1$，在二处等于 $1-2^{-k}<1$。方程两种形式相乘即可互换。

不需要额外谱理论即可得到全体 $N$ 的界
$$
\lambda_k^N\le G_N\le B_k\lambda_k^N,
\qquad
B_k=(2/\lambda_k)^{k-1}.
\tag{TM.383}
$$
初始 $0\le j<k$ 时，比值 $G_j/\lambda_k^j=(2/\lambda_k)^j$ 位于 $[1,B_k]$。序列 $G_N$ 与 $\lambda_k^N$ 满足同一个正系数递推；把已有上下界相加就归纳得到下一步。结合式（TM.376），
$$
N\log\lambda_k\le\log|\mathcal W_N^{(k)}|
\le N\log\lambda_k+(k-1)\log(2/\lambda_k),
\qquad
\lim_{N\to\infty}\frac{\log|\mathcal W_N^{(k)}|}{N}=\log\lambda_k.
\tag{TM.384}
$$
令 $N_k(m)=\min\{N:G_N\ge m\}$。由于 $m>1$，有 $N_k(m)\ge1$，且 $G_{N_k(m)-1}<m\le G_{N_k(m)}$。将式（TM.383）代入左右两边，得到
$$
\log m-(k-1)\log(2/\lambda_k)
\le N_k(m)\log\lambda_k
<\log m+\log\lambda_k.
\tag{TM.385}
$$
所以固定 $k$ 时，所需完整词长满足 $N_k(m)\log\lambda_k=\log m+O_k(1)$。这是长度与可区分整数数目的关系，不是说各编码的同深度前缀可以互相恢复。

计数的对数是均匀律下的最大 Shannon 熵；未指定概率律时，式（TM.384）是语言增长率。若 $G_N>m$，实际标准余数代码集仍只有 $m$ 个元素，不能用全部 $G_N$ 个合法词代替这项实验的样本空间。

#### 1.2.5 编码自身就是分辨率结构：完整双射不保证有限截断可运输

把每个规范整数词按低位在前排列，并在高位一侧无限补零。定义 $q_{k,N}(n)$ 为前 $N$ 个低位。此处的读数合同不包含总词长或终止符。随着 $N$ 增大，旧读数可从新读数取前缀恢复；全部读数联合起来能唯一确定整数，但任一固定 $N$ 只有有限个读数。

对两个编码 $k,\ell$，目标深度 $N$ 能由源深度 $M$ 统一恢复，当且仅当
$$
q_{\ell,N}=F\circ q_{k,M}\ \text{对某个 }F\text{ 成立}
\quad\Longleftrightarrow\quad
\ker q_{k,M}\subseteq\ker q_{\ell,N}.
\tag{TM.386}
$$
这里的核关系指两个整数具有相同读数。必要性直接来自函数复合；充分性是在每个实际源读数的纤维上，把 $F$ 定义为其公共目标读数，核包含保证定义无歧义。若把 $F$ 定义在更大的读数载体上，其非实际像上的取值不影响结论。

同深度的分割一般不可比。写 $q_{\mathrm{bin},N}$ 为普通二进制读数：在深度二，整数零与三具有相同的 Zeckendorf 低两位 $00$，二进制低两位却分别为 $00$、$11$；整数零与四具有相同的二进制低两位 $00$，Zeckendorf 中四等于 $G_2+G_0$，低位在前的低两位为 $10$，与零不同。因而
$$
\ker q_{2,2}\not\subseteq\ker q_{\mathrm{bin},2},
\qquad
\ker q_{\mathrm{bin},2}\not\subseteq\ker q_{2,2}.
\tag{TM.387}
$$
更强的障碍可精确写成整除条件。固定模数 $L>1$，则
$$
n\longmapsto n\bmod L\ \text{经 }q_{k,N}\text{ 因子化}
\quad\Longleftrightarrow\quad
L\mid G_j\quad\text{对全部 }j\ge N.
\tag{TM.388}
$$
必要性：对每个 $j\ge N$，零与整数 $G_j$ 的低 $N$ 位均为零，而 $G_j$ 的唯一规范表示是第 $j$ 位单独为一。若余数可恢复，必有 $G_j\equiv0\pmod L$。充分性：把任意整数的有限展开拆成前 $N$ 项与余下项；假设使所有余下项模 $L$ 为零，因此余数等于已读低位的加权和。

对每个固定有限 $k\ge2$，式（TM.388）的右侧对任何 $L>1$、任何有限 $N$ 都不成立。为证明这一点，模 $L$ 的连续 $k$ 项权重按“左移并添入总和”更新；此更新可逆，逆运算是“用末项减去其余各项以恢复最早一项”。若全部尾项为零，则某个连续 $k$ 项向量为零；反复逆推会使初始向量也为零，与 $G_0=1\not\equiv0\pmod L$ 矛盾。下一小节给出这一逆运算的完整公式。

普通二进制的相应整除条件则为
$$
n\bmod L\text{ 可由 }q_{\mathrm{bin},N}(n)\text{ 恢复}
\quad\Longleftrightarrow\quad L\mid2^N.
\tag{TM.389}
$$
因为它要求 $L$ 整除全部 $2^j$、$j\ge N$，等价于只要求整除第一项。二进制最低位天然适配二的幂模数；固定有限 k-bonacci 的最低位截断不具备任何非平凡模数的统一有限读出。素数及素数幂分辨率应由实际商映射声明，不能只由编码字符形式认定。

Zeckendorf 的奇偶反例还能区分有限解码与完成化。取 Fibonacci 约定 $F_1=F_2=1$，则 $G_j=F_{j+2}$。递推模二的权重依次为 $1,0,1,1,0,1,\ldots$，周期三。因此
$$
G_{3t}\equiv1\pmod2,\qquad G_{3t+1}\equiv0\pmod2.
\tag{TM.390}
$$
对每个固定 $N$，当 $3t\ge N$ 时，$G_{3t}$ 与零的低 $N$ 位相同，却有不同奇偶性。在按低位前缀给出的名字拓扑中，$G_{3t}$ 因而趋向零；在二进制名字拓扑中，其最低位始终为一，不趋向零。

所以，把同一个整数从 Zeckendorf 名字改成二进制名字的双射，不连续于这一低位名字拓扑的零点，也不存在与该双射相容的连续完成化映射。这里两侧的无限名字均按低位在前、有限词无限补零理解；若读数已包含完整总长度，不能照搬这个趋零论证。

即使有限读数附带“是否已经结束”，仍然没有恢复奇偶性的统一有限 lookahead：给定 $N$，取 $3t>N$；整数 $G_{3t}$ 与 $G_{3t+1}$ 的前 $N$ 位均为零，且都尚未结束，但奇偶性不同。逐个读完整有限词之后当然仍可解码；失败的是对所有输入共同有效的有限读取预算。

可据式（TM.386）定义从一塔到另一塔的深度代价
$$
M_{k\to\ell}(N)=
\inf\{M\in\mathbb N:\ker q_{k,M}\subseteq\ker q_{\ell,N}\},
\qquad\inf\varnothing=+\infty.
\tag{TM.391}
$$
它测量最坏情况下的统一有限深度，不等于给定整数的实际解码步数；例如 $M_{2\to\mathrm{bin}}(1)=+\infty$。编码参数改变的不仅是记号长度，也包括有限访问怎样分割共同整数源。

这一深度代价可以递归复合。若 $a=M_{\ell\to\nu}(N)$ 与 $b=M_{k\to\ell}(a)$ 都有限，自然数中的最小值可取到，故 $\ker q_{k,b}\subseteq\ker q_{\ell,a}\subseteq\ker q_{\nu,N}$，从而 $M_{k\to\nu}(N)\le M_{k\to\ell}(M_{\ell\to\nu}(N))$。这给多层译码一份实际读取上界，也允许某一层因核包含失败而具有无限代价。不同读数的共同细化可由配对读数实现，其核为各核的交；因此整个组织可以是互补观察的有向网，而不必只有单条深度链。深度与递归调用顺序在此是观察协议的结构，尚未赋予外置物理时间的含义。

#### 1.2.6 余数与连续一长度还缺一个权重相位

现在把目标切换为实际有限词的逐位运行，采用低位先读。在读完 $j$ 位后，令
$$
r_j=\sum_{i<j}b_iG_i\pmod m,\qquad
s_j=\text{已读序列末尾连续一的长度}.
\tag{TM.392}
$$
$s_j$ 足以控制下一位的禁词合法性，却不包含下一位应使用哪个权重。状态 $(r_j,s_j)$ 可以用于把深度 $j$ 另作外部参数的非自主动态规划，但不能无条件跨深度合并为自主状态。

例如 $k=2,m=5$：低位前缀 $(0)$ 在深度一、前缀 $(0,0)$ 在深度二，都给出 $(r,s)=(0,0)$。各自追加一后，余数分别变为 $G_1=2$ 与 $G_2=3\pmod5$。这些是低位读取前缀，不是可以从最高位一侧删除的前导零。

一个足够的有限相位状态是
$$
w_j=(G_j,G_{j+1},\ldots,G_{j+k-1})\pmod m\in R_m^k,
\qquad
w_{j+1}=M w_j,
\tag{TM.393}
$$
其中
$$
M(w_0,\ldots,w_{k-1})
=(w_1,\ldots,w_{k-1},\sum_{i=0}^{k-1}w_i),
\qquad
\det M=(-1)^{k-1}.
\tag{TM.394}
$$
不用假定 $m$ 为素数，它已有显式逆
$$
M^{-1}(v_0,\ldots,v_{k-1})
=(v_{k-1}-\sum_{i=0}^{k-2}v_i,v_0,\ldots,v_{k-2}).
\tag{TM.395}
$$
直接代入两种复合均为恒等。因而 $M$ 是有限集合 $R_m^k$ 上的置换。从实际初始向量 $w_0=(1,2,\ldots,2^{k-1})\bmod m$ 出发，抽屉原理给出两个相等迭代；利用较早次迭代的逆，把这一相等退回初始点，即得从起点开始的纯周期，而不只是最终周期。存在 $1\le P_{k,m}\le m^k$ 使 $w_{j+P_{k,m}}=w_j$。

完整自主状态可取 $(r,s,w)$，其中 $w$ 只需在上述实际轨道上变化。对允许数字 $b$ 的更新为
$$
r'=r+bw_0,\qquad
s'=\begin{cases}0,&b=0,\\s+1,&b=1,\end{cases}
\qquad w'=Mw.
\tag{TM.396}
$$
零始终合法，一仅在 $s<k-1$ 时合法。初始 $r=s=0$。若要求总函数，可另加拒绝态。相同完整状态面对相同后续词，每一步有相同合法性、相同后继状态，因而有相同终态余数；这是逐词长归纳所得的任务充分性。也可用 $j\bmod P_{k,m}$ 代替 $w$，状态数上界为 $mkP_{k,m}$，不声称这是最小自动机。

这一状态服务于“读完后求余数”的任务。它没有推翻上一小节的有限深度障碍：状态机可以一直读取到结束，但其存在不提供对任意整数统一有界的终止深度。

#### 1.2.7 强制零不能裸删除，覆盖也不能提前成为吸收事件

当 $s=k-1$ 且还要继续读入时，下一位必须为零。但这一步仍会重置 $s$、推进权重相位 $w$、消耗一次数字时间。$k=2$ 的低位词 $(1,0,1)$ 给出
$$
G_0+G_2=4,\qquad
G_0+G_1=3.
\tag{TM.397}
$$
两者的差别正是直接删除中间零却不保留位权推进造成的。因此局部条件分支熵为零，并不意味着这个操作是恒等、耗时为零，或可以从所有观察协议中删除。若已有同一完整状态与同一深度，这一步可预测，故不会额外切分该条件纤维；但不同相位、停止条件或跨状态的全局观察仍需另判。

终态覆盖也不能只因某个数字前缀当前的部分和值落在 $C_m$ 中就剪枝。取 $k=2,m=5,C_5=\{1\}$。低位前缀一的部分余数为一；继续合法读入零、一，得到通常高位在前打印的词 $101$，数值为四，最终余数是幸存者。提前删除前缀一会删掉这个真实结果。

给定前缀 $h$，把规定的剩余长度、规范终止规则、代表元范围等全部限制写入合法完成集 $\mathcal E(h)$。安全删除所需条件是
$$
\forall v\in\mathcal E(h),\qquad
\operatorname{val}_k(hv)\bmod m\in C_m.
\tag{TM.398}
$$
此处 $hv$ 按实际低位读取位置连接，不将后续词从零号权重重新开始。只检查当前部分余数在 $C_m$ 中，不足以推出全称条件。

#### 1.2.8 首返宏块如何保留终止、算术与时间

先仅按读取顺序讨论语法，不预设高位还是低位在前。定义完整首返块 $B_j=1^j0$、$0\le j<k$，终止尾 $R_r=1^r$、$0\le r<k$。每个合法有限词唯一分解为
$$
w=B_{j_1}\cdots B_{j_n}R_r.
\tag{TM.399}
$$
证明是把每个零与紧邻此前、上一个零之后的全部一归为一块，最后一个零之后留作尾。零的位置唯一决定分割；禁词规则保证每段一的长度小于 $k$。反向拼接合法，因为每个完整块以零结束。没有零的词对应零个完整块及一份终止尾。

$k=2$ 时完整块为零与 $10$，终止尾为空或一。只保留自由二元块列表而删去尾，会混同空词与一、零与 $01$。一般 $k$ 的分组是首返结构；只有读到连续 $k-1$ 个一后，继续读入的零才是强制步。

设原系统的部分更新为 $T_0,T_1$，复合右侧先执行。宏更新、长度与尾更新分别为
$$
M_j=T_0\circ T_1^{\,j},\qquad
\ell_j=j+1,\qquad
T_{\mathrm{tail},r}=T_1^{\,r},\qquad
|w|=\sum_{s=1}^{n}\ell_{j_s}+r.
\tag{TM.400}
$$
复合合法性要求全部中间更新有定义，不能只看最终状态。合法终止尾也不要求还可以执行一次返回零。若任务允许在块内停止、读取或干预，必须保留相应端口或块内位置；只保留块边界，对所有原始时刻的实验未必充分。

对一条实际路径的边权 $a_u$、相位增量 $\theta_u$、费用 $c_u$ 与时长 $t_u$，宏边应携带
$$
A_B=\prod_{u\in B}a_u,\qquad
\Theta_B=\sum_{u\in B}\theta_u,\qquad
C_B=\sum_{u\in B}c_u,\qquad
T_B=\sum_{u\in B}t_u.
\tag{TM.401}
$$
矩阵或通道权重使用有序复合；费用可按向量逐项累加；相位可按模 $2\pi$ 理解。随机权重须取实际路径概率，不能擅自重新归一化。每原始位耗时一且相位为 $e^{i\omega}$ 时，零块与 $10$ 块分别携带 $e^{i\omega}$、$e^{2i\omega}$，把两者改成同一个单位相位已改变实验。

采用实数分数位权 $V_\beta(d_1\cdots d_Q)=\sum_{u=1}^{Q}d_u\beta^{-u}$、$\beta>1$ 时，有
$$
V_\beta(uv)=V_\beta(u)+\beta^{-|u|}V_\beta(v),\qquad
V_\beta(B_j)=\sum_{u=1}^{j}\beta^{-u}.
\tag{TM.402}
$$
故宏符号除了局部值，仍须保留长度才能运输后续位权。这也解释了为什么不能把宏标签直接当普通二进制整数位：高位在前 Zeckendorf 词 $10$ 表示二，而单个标签一按普通二进制只表示一。

对高位在前的 Zeckendorf 整数词 $d_1\cdots d_n$，可显式携带二维算术状态
$$
A_n=\sum_{u=1}^{n}d_uF_{n-u+1},\qquad
V_n=\sum_{u=1}^{n}d_uF_{n-u+2},\qquad
\binom{A_{n+1}}{V_{n+1}}
=\begin{pmatrix}0&1\\1&1\end{pmatrix}\binom{A_n}{V_n}
+d_{n+1}\binom11.
\tag{TM.403}
$$
这里 $V_n$ 是整数值。第一坐标更新来自原来各项的权重前移一阶，第二坐标更新来自 Fibonacci 递推；新最低位贡献 $(d,d)$。若记矩阵为 $Q$，宏零为 $u\mapsto Qu$，宏 $10$ 为 $u\mapsto Q^2u+(1,2)^{\mathsf T}$，终止尾一为 $u\mapsto Qu+(1,1)^{\mathsf T}$。这与前面的低位先读相位状态是两套明确不同的读取合同；两者都保留真实数值，而不把零误当恒等。

#### 1.2.9 同一词语言的两种时钟与精确熵缺口

令 $A_N$ 为长度恰好为 $N$ 的合法原始词数。唯一分解（TM.399）给出形式幂级数恒等式
$$
\sum_{N\ge0}A_Nz^N
=\frac{1+z+\cdots+z^{k-1}}{1-z-z^2-\cdots-z^k}.
\tag{TM.404}
$$
分子枚举终止尾；完整块的长度生成函数是 $z+\cdots+z^k$，任意有限块列表给其几何级数。若每个零、一分别携带常数复权重 $x_0,x_1$，同理分子改为 $\sum_{r=0}^{k-1}(x_1z)^r$，分母改为 $1-\sum_{j=0}^{k-1}x_1^jx_0z^{j+1}$。复权重可能抵消，不能直接当成正的计数或概率。

式（TM.404）也给 $A_N=2^N$ 对 $N<k$、$A_N=\sum_{h=1}^k A_{N-h}$ 对 $N\ge k$，与区间双射所得 $A_N=G_N$ 一致。原始位时钟下的增长率为 $\log\lambda_k$。固定完整宏块数 $n$ 并以零结束时，恰有 $k^n$ 个块词，每宏步的增长率是 $\log k$；若允许全部 $k$ 个终止尾，只多固定因子 $k$。这些量使用不同时间分母。

保留长度函数后，原始增长率 $h=\log\lambda_k$ 满足首返方程
$$
\sum_{j=0}^{k-1}e^{-h\ell_j}=1,\qquad\ell_j=j+1.
\tag{TM.405}
$$
现在在宏字母表上指定独立同分布律 $p=(p_0,\ldots,p_{k-1})$，令 $\bar\ell=\sum_jp_j\ell_j$，$H(p)=-\sum_jp_j\log p_j$，零项按零处理。令 $q_j=\lambda_k^{-\ell_j}$；式（TM.405）保证 $q$ 为严格正的概率律。展开相对熵得到
$$
D(p\Vert q)=\bar\ell\log\lambda_k-H(p),\qquad
\frac{H(p)}{\bar\ell}
=\log\lambda_k-\frac{D(p\Vert q)}{\bar\ell}
\le\log\lambda_k.
\tag{TM.406}
$$
等号当且仅当 $p=q$。有限字母表的大数定律使长块串的负对数概率除以实际总原始长度，几乎处处趋于 $H(p)/\bar\ell$；所以这一式确实比较同一 iid 块实验在两种时钟下的渐近信息率。

$k=2$ 时最优块律为 $(\phi^{-1},\phi^{-2})$，对应长度一和二。若均匀取两个宏符号，平均长度为 $3/2$，每原始位的信息率为 $\tfrac23\log2<\log\phi$；严格性也来自均匀律不等于 $q$。这不是可逆编码平白创造或销毁信息，而是概率律与时间标度必须一起运输。有限终止尾长度小于 $k$，固定 $k$ 下不改变长路径的上述极限，但精确有限任务仍不可丢掉它。

#### 1.2.10 终态自动机的可达性与循环判据

高位在前读取也有不能提前剪枝的实例。Zeckendorf 合法前缀 $100$ 表示三，属于 $0\bmod3$；其合法延长 $1000$ 表示五，离开该覆盖类。原始终态谓词不是自动吸收事件。正确的有限识别器必须保留必要的非接受中间状态，并在终止时判定。

对任意有限自动机，接受语言非空当且仅当某个接受状态从起点可达；接受有限词有任意大长度，当且仅当存在一个从起点可达、并且还能到达接受状态的非空有向循环。前一断言就是接受路径定义。后一断言的正向证明是在足够长的接受路径上找重复状态，重复段构成所需循环；反向证明则是在相同进入与离开路径之间任意多次重复该循环。每条边读取一个字母；宏边可使用严格正的有限长度，结论相同。

因此，自动机无循环不等于语言为空，一条到接受终点的单边路径已经给出反例。但有限同余覆盖有一个额外结构：若 $S_m\ne\varnothing$，某个幸存剩余类 $r$ 给出无穷多个互异整数 $r+tm$。若一个有限自动机确实识别全部规范整数编码的幸存者，每个这些整数都有有限代码、一个词不能代表两个整数，则其接受词数无穷，因有限字母表而词长无界。于是对这样的完整识别器有
$$
S_m\ne\varnothing
\quad\Longleftrightarrow\quad
\text{存在起点可达且可通向接受状态的非空循环}.
\tag{TM.407}
$$
反向使用一个接受词即可得到真实幸存整数；正向使用的是有限同余任务的周期性。这个加强不适用于任意语言、无限同余族，或只识别标准代表元 $0,\ldots,m-1$ 的有限代码集。它也不能修复因误删“当前已覆盖”状态而失真的识别器。前导零、零的表示、读取方向、位权推进及终止尾均属于识别忠实性的条件。

#### 1.2.11 实际模约化与跨编码运输的交换图

在固定模数 $m$ 上，完整标准代码之间有可逆运输
$$
R_m^{k,\ell}=E_{\ell,m}\circ E_{k,m}^{-1}:
\mathcal C_{k,m}\overset{\sim}{\longrightarrow}\mathcal C_{\ell,m}.
\tag{TM.408}
$$
若 $m\mid M$，存在实际剩余类约化 $\pi_{m,M}:R_M\to R_m$。在编码上的正确分辨率下降为
$$
\rho_{m,M}^{(k)}=E_{k,m}\circ\pi_{m,M}\circ E_{k,M}^{-1}.
\tag{TM.409}
$$
它先解码原剩余类、作真实模约化、再重新编码，不默认等于删除若干高位。两种编码与模数下降组成交换关系
$$
R_m^{k,\ell}\circ\rho_{m,M}^{(k)}
=\rho_{m,M}^{(\ell)}\circ R_M^{k,\ell}.
\tag{TM.410}
$$
因为两边展开都等于 $E_{\ell,m}\circ\pi_{m,M}\circ E_{k,M}^{-1}$。同样，模约化的恒等与复合律也通过双射运输。

条件 $m\mid M$ 不能换成仅有 $m<M$：整数映射 $n\mapsto n\bmod m$ 能从 $n\bmod M$ 因子化，必要性比较零与 $M$，立即要求 $m\mid M$；充分性是通常模约化。即使利用标准代表元另行定义了一个集合函数，也不等于所有整数上的这项因子化。

即使整除关系合法，数字截断仍不等于模约化。取 $k=2,M=6,m=3$，标准代表元五编码为 $1000$，因为 $G_3=5$。其最低两位为 $00$，表示零；但真实约化为
$$
5\bmod3=2,\qquad E_{2,3}(2)=10.
\tag{TM.411}
$$
普通二进制最低 $N$ 位实现模 $2^N$，原因是全部更高位权可被 $2^N$ 整除；一般 k-bonacci 位权没有这一性质。真实模数塔可以完整地跨编码运输，编码最低位前缀塔却不因此等于该模数塔。

#### 1.2.12 幸存任务不随表示丢失；动力学必须明确是否真的共轭

定义 $\mathcal C_{k,m}^{\mathrm{cov}}=E_{k,m}(C_m)$ 与 $\mathcal S_{k,m}=E_{k,m}(S_m)$，它们无交地分割实际标准代码集。式（TM.408）给出
$$
R_m^{k,\ell}(\mathcal S_{k,m})=\mathcal S_{\ell,m},
\qquad |\mathcal S_{k,m}|=|S_m|.
\tag{TM.412}
$$
若共同剩余变量 $R$ 的律为 $\mu$，各代码律必须取 $E_{k,m}$ 的推前。于是幸存概率、终态指示函数的期望，以及这份有限随机变量的 Shannon 熵都保留：
$$
\Pr(E_{k,m}(R)\in\mathcal S_{k,m})=\Pr(R\in S_m),
\qquad H(E_{k,m}(R))=H(R).
\tag{TM.413}
$$
第一式来自事件原像完全相同；第二式来自双射只重新标记概率质量。

若原剩余空间上还有实际动力学 $T:R_m\to R_m$，其真正运输是
$$
T^{(k)}=E_{k,m}TE_{k,m}^{-1},\qquad
(T^{(k)})^n=E_{k,m}T^nE_{k,m}^{-1}.
\tag{TM.414}
$$
第二式由逐次消去中间的逆与正映射得到，故对应轨道与周期保持。若概率律、实际时钟和观测也一致运输，不能把纯表示共轭称为改变了同一实验的相应信息不变量。

不同编码自身的原始数字读取、删位与单位移位，尚未由式（TM.414）证明共轭。它们可以具有不同的语言增长率、相位周期、局部运算与规范化成本。一个直接反例是：全部无限二进制词的左移有两个不动点，即全零和全一；固定有限 $k$ 的禁 $1^k$ 移位只有全零不动点。共轭会保持不动点个数，因此这两种原始单位移位不能由任意双射共轭。完整数值任务的运输与数字时间动力学的运输，必须各有其交换关系。

#### 1.2.13 k 的离散族、有限窗口二进制极限与无限完成

固定有限长度 $N$，只要 $k>N$，禁词不会出现，而且全部所用位权都在初始二进制段内，故
$$
\mathcal W_N^{(k)}=\{0,1\}^N,\qquad
\operatorname{val}_k(b)=\sum_{j<N}b_j2^j.
\tag{TM.415}
$$
这是精确稳定，不只是近似。任意固定整数最终具有与普通二进制相同的规范词。条件 $k=N$ 不够，因为长度 $N$ 的全一词仍被禁止。$k$ 是整数参数及其极限，没有在此定义一个随实参数连续旋转的编码族。

根随 $k$ 严格增加：在 $\lambda_k$ 处为倒数幂和增加一项会使和大于一，下一根必须向右移动。由特征方程乘以 $\lambda_k-1$，有
$$
\lambda_2=\phi,\qquad
2-\lambda_k=\lambda_k^{-k}\le\phi^{-k},\qquad
\lambda_k\uparrow2.
\tag{TM.416}
$$
但固定任何有限 $k$ 后，足够长窗口仍有约束，语言增长率仍严格小于 $\log2$。有限窗口的最终稳定，不等于某个统一有限 $k$ 容纳全部无限词。

令 $\mathcal K_k\subseteq\{0,1\}^{\mathbb N}$ 为不含 $1^k$ 的无限低位名字空间，以前缀乘积拓扑度量。它是闭的紧空间；补零的规范整数名字在其中稠密，因为任意合法有限前缀都可接全零尾，得到一个整数名字。不同名字的距离取 $2^{-j}$，其中 $j$ 是首次不同的位号，同一名字的距离取零；$\mathcal K_k$ 因此正是这些整数名字的度量完成。它是符号名字的完成，而非自动收敛的实数级数 $\sum_j b_jG_j$；解释为任何指定实数或 p-进数，仍需另证该解码的收敛与相容性。

无限语言之并 $\bigcup_{k\ge2}\mathcal K_k$ 仅包含一的游程具有统一有限上界的序列。它在全部二进制无限词中稠密，因为任意有限前缀后接全零即可进入某个 $\mathcal K_k$，但它并不等于全部空间。具有任意长一游程的无限词不属于任何固定层。若把宏块字母表扩为全部 $1^j0$、$j\ge0$，还须单独处理最终永远为一的词；只用无穷完整返回块不会覆盖它们。

这里还出现一个可量化的极限顺序区别：对每个固定有限 $k$，任意低位有限 cut 都不能统一给出奇偶性；在二进制端点，第一位就能给出。有限窗口的逐点稳定并不保持对所有整数的统一读取预算，不能把“每个固定数最终变成二进制名字”改写成“存在一个固定有限阶编码已拥有全部二进制分辨能力”。

#### 1.2.14 全塔识别、有限观察与对角逃逸的不同量词

对补零的整数名字，全部有限读数联合起来是单射：两个整数不同，其有限规范词在某一位不同。但任何固定深度只有有限个读数，而整数源无限，所以该深度的读数不可能单射。这两句分别具有量词
$$
\forall x\ne y\ \exists N:\ q_{k,N}(x)\ne q_{k,N}(y),
\qquad
\neg\exists N\ \forall x\ne y:\ q_{k,N}(x)\ne q_{k,N}(y).
\tag{TM.417}
$$
抽屉原理说明固定有限读数不能区别所有整数；它没有说明每个任务都需要无限细化。一个有限状态就能完整保留的终态任务，可以在任务商上闭合。重复读取或已由旧读数确定的强制位也不必增加目标信息。

完成化增加的是相容无限线程，不是“新添的有限整数”。最小例子已有 $\mathcal K_2$：任意无限二进制序列 $b$ 经交错补零映射为
$$
\iota(b)_{2n}=b_n,\qquad \iota(b)_{2n+1}=0.
\tag{TM.418}
$$
所得词没有相邻一且映射单射，故 $\mathcal K_2$ 含有全部二进制无限序列的一份副本。也可直接给出合法空间内的对角论证：若列出任意可数序列 $s^{(0)},s^{(1)},\ldots\in\mathcal K_2$，定义
$$
t_{2n}=1-s^{(n)}_{2n},\qquad t_{2n+1}=0.
\tag{TM.419}
$$
每个一之后都有零，所以 $t\in\mathcal K_2$；它在第 $2n$ 位与第 $n$ 个列举词不同，因此不在列表中。规范有限整数词可数，合法完成名字不可数，二者的差别由这份具体构造承担。相同论证也适用于所有 $k\ge2$，因为这些构造都无相邻一。

这个对角命题不附带可计算性保证：任意被列出的无限序列未必以有效方式提供其数字。有限递归状态机、完成化或自我引用本身，也不会自动给出 Gödel 不完备性；后者还涉及有效公理化、一致性及足够算术表达能力等明确条件。有限步骤与完成对象可以是同一相容结构的两种表示，但“同一”须指明是联合确定、可逆解码、连续延拓还是有限预算可恢复。本节的反例显示这些关系不能互相替代。

#### 1.2.15 已有归属与适用范围

整数与增长部分以下列不可变源码快照为定位依据：`19a8543ea50538700a993a51989d9cbc7b5bf4fd`。

- `D5/S0/Tower/DBonacci/Names.lean` 中 `dbonacci d (N+2)` 对应本节 $G_N$；`DBonacciAdmissible` 定义禁连续 $d$ 个一；`dbonacci_name_card` 给一般合法词计数。计数声明本身不等于指定整数值映射的双射，式（TM.376）的区间归纳明确承担后者。
- `D5/S0/Tower/Tribonacci/Representation.lean` 中 `decode` 使用 $1,2,4,7,\ldots$，`decode_lt_tribonacci`、`decode_bijective`、`decodeEquiv` 与 `encode` 已拥有 $k=3$ 整数情形的范围与双射；本节没有把这一专门化冒称一般 $k$ 源码已全部形式化。
- `D5/S0/Tower/DBonacci/Values.lean` 的 `dbonacciWordValue` 使用 `dbonacciPerronRoot d` 的负幂实数权重，对应式（TM.402）类型的任务，不是式（TM.375）的整数解码。
- `D5/S0/Tower/DBonacci/PerronRoot.lean` 已包含正根存在唯一性、特征方程、`two_sub_dbonacciPerronRoot_eq_inv_pow`、根的严格递增、二阶黄金根与 `dbonacciPerronRoot_tendsto_two`。这些成熟接口不因本节使用而成为新增形式化成果。
- RRO 第 132.2 节的连续一后缀接口、计数矩阵、增长根与任务界面区别，提供禁词任务的背景。后缀长度处理合法性；加上模数值任务时，式（TM.392）的反例说明仍需运输位权相位。

首返宏块部分以下列不可变源码快照为定位依据：`9d416050c9a90f785d50f2a5034f1a1f99334d62`。它与整数及增长部分采用的 `19a8543ea50538700a993a51989d9cbc7b5bf4fd` 是两个不同快照，各自仅承担所列源码定位与结论范围。

- `D5/S0/Automata/TypedPartialDFAOOverBase.lean` 的 `runTransition` 按列表头到尾读取，`evalFrom_append` 与 `runFrom_append` 给部分运行的有序拼接。
- `D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.lean` 的 `expand` 展开零、$10$ 与终止尾；`decode_expand`、`expandCode_injective`、`expand_compressLegalWord`、`compressLegalWord_expand` 给该代码层双向关系。其 `LegalWord` 定义为展开像，禁止相邻一的独立语言刻画还须结合下一项。
- `D5/S0/Automata/BinaryZeckendorfLanguage.lean` 的 `base_success_iff_noAdjacentOnes` 对应成功运行与无相邻一；`BinaryZeckendorfBlockSkeleton.lean` 的 `eval_extractSkeleton` 与 `eval_extractSkeleton_start` 给 skeleton 的精确输出对应。这些声明不自动包括本节全部费用、相位、时长和熵率结论。

本节的新增组织包括：一般整数区间归纳、编码前缀与模数读取的整除判据、可逆权重相位状态、终态剪枝边界、首返费用与 iid 块熵率运输，以及有限窗口与无限完成的量词区分。它们在所列模型中由正文证明支持；没有声称原创性，没有把数学编码层直接等同为物理空间、物理时间或量子过程。

### 1.3 Numeration and weighted continuation quotients

#### 1.3.1 Legal numeration languages

**定义 1.1。** Fix an integer $k\ge 2$. Define
$$
G_i=2^i\quad(0\le i<k),
\qquad
G_{n+k}=G_{n+k-1}+\cdots+G_n\quad(n\ge0).
\tag{TM.524}
$$
Let $\mathcal L_k\subseteq\{0,1\}^*$ consist of the words containing no factor $1^k$. In most-significant-digit order, put
$$
\operatorname{val}_k(d_{n-1}\cdots d_0)
=\sum_{j=0}^{n-1}d_jG_j.
\tag{TM.525}
$$
The canonical greedy representation $\operatorname{rep}_k(n)$ has no leading zero when $n>0$, and $\operatorname{rep}_k(0)=\varepsilon$. Arbitrary leading-zero padding gives
$$
\mathcal L_k=0^*\operatorname{rep}_k(\mathbb N).
\tag{TM.526}
$$
For an integer $L\ge1$, define the unbounded divisibility language
$$
\mathcal A_{k,L}
=\{w\in\mathcal L_k:\operatorname{val}_k(w)\equiv0\pmod L\}
=0^*\operatorname{rep}_k(L\mathbb N).
\tag{TM.527}
$$
The empty word and every all-zero word belong to this language. Illegal words are rejected. A trim deterministic automaton omits the state whose right language is empty; its transition function can therefore be partial.

**定理 1.2（Charlier–Rampersad–Rigo–Waxweiler）。** For $k\ge2$ and $L\ge2$, the minimal trim most-significant-digit automaton recognizing $\mathcal A_{k,L}$ has exactly
$$
kL^k
\tag{TM.528}
$$
states. A state reached after $w$ is determined by its legality state and the residue vector
$$
\bigl(
\operatorname{val}_k(w),
\operatorname{val}_k(w0),\ldots,
\operatorname{val}_k(w0^{k-1})
\bigr)\pmod L.
\tag{TM.529}
$$
This is Corollary 19, printed page 55, of *State Complexity of Testing Divisibility*, arXiv:1008.1668v1, DOI [10.4204/EPTCS.31.7](https://doi.org/10.4204/EPTCS.31.7). The language in that result is $0^*\operatorname{rep}_U(L\mathbb N)$; the modulus need not be prime or odd. The explicit residue-state description follows on printed pages 55–56. [Original source](https://arxiv.org/pdf/1008.1668v1).

**推论 1.3。** The complete minimal DFA for $\mathcal A_{k,L}$ has $kL^k+1$ states. For $L=1$, the trim and complete counts are respectively $k$ and $k+1$.

**Proof.** There are illegal words, and they all have empty right language. Completing the trim minimal automaton adds exactly this one state. When $L=1$, the language is $\mathcal L_k$; its $k$ live states record the trailing run of ones. Runs $a<b$ are distinguished by the continuation $1^{k-b}$, which is legal from $a$ and illegal from $b$. $\square$

#### 1.3.2 Binary divisibility and converter memory

**命题 1.4。** If $L$ is a positive odd integer, the padded binary divisibility language
$$
\mathcal B_L
=\{w\in\{0,1\}^*:\operatorname{val}_{\mathrm{bin}}(w)\equiv0\pmod L\}
\tag{TM.530}
$$
has a complete minimal DFA with exactly $L$ states. Here $\operatorname{val}_{\mathrm{bin}}$ denotes ordinary binary evaluation, including $\operatorname{val}_{\mathrm{bin}}(\varepsilon)=0$.

**Proof.** Use residues $r\in\mathbb Z/L\mathbb Z$, initial and accepting residue $0$, and digit transitions
$$
r\longmapsto2r+d\pmod L.
\tag{TM.531}
$$
Every residue is reachable by the binary representation of a representative in $\{0,\ldots,L-1\}$. For distinct residues $r,s$, choose $t$ with $2^t\ge L$, and take $0\le y<L$ satisfying $y\equiv-2^tr\pmod L$. The length-$t$ padded binary representation of $y$ accepts from $r$. It rejects from $s$ because
$$
2^ts+y\equiv2^t(s-r)\not\equiv0\pmod L,
\tag{TM.532}
$$
as $2$ is invertible modulo odd $L$. $\square$

**命题 1.5（subsequential conversion with exact legal domain）。** Let $L$ be odd. Suppose an $S$-state deterministic partial subsequential transducer has domain exactly $\mathcal L_k$ and emits a binary word with the same numerical value as its input. Then
$$
SL\ge kL^k,
\qquad S\ge kL^{k-1}.
\tag{TM.533}
$$
The same conclusion holds if output correctness is required only modulo this particular $L$, while the domain remains exactly $\mathcal L_k$.

**Proof.** Compose the transducer with the $L$-state binary residue automaton. The product states are $(q,r)$. If a transducer transition emits a chunk $v$, update
$$
r\longmapsto2^{|v|}r+\operatorname{val}_{\mathrm{bin}}(v)\pmod L.
\tag{TM.534}
$$
Incorporate any initial output into the initial residue. If state $q$ has terminal output $\omega(q)$, declare $(q,r)$ accepting precisely when
$$
2^{|\omega(q)|}r+\operatorname{val}_{\mathrm{bin}}(\omega(q))\equiv0\pmod L.
\tag{TM.535}
$$
A state without terminal output is nonaccepting. Thus terminal chunks require an acceptance test, not additional states. The product is a partial deterministic automaton with at most $SL$ trim states, and its language is exactly $\mathcal A_{k,L}$. Apply the preceding state-count theorem. $\square$

**命题 1.6（conversion under a legality promise）。** Suppose instead that an $S$-state subsequential transducer is defined and correct on every word of $\mathcal L_k$, with no restriction on its behavior on illegal words. Then the same argument, after intersection with the $k$-state partial legality automaton, gives
$$
kSL\ge kL^k,
\qquad S\ge L^{k-1}
\tag{TM.536}
$$
for odd $L$.

**Proof.** The legality automaton removes every illegal input, so the triple product recognizes exactly $\mathcal A_{k,L}$ and has at most $kSL$ trim states. $\square$

**推论 1.7。** There is no fixed finite-state subsequential transducer that converts every legal $k$-bonacci representation to an equal-valued binary representation in these reading conventions, even when legality is only promised.

**Proof.** The inequality $S\ge L^{k-1}$ holds for every positive odd $L$, whereas $S$ is fixed. $\square$

**注 1.8。** These bounds concern inputs representing all natural numbers, of unbounded length. If the domain is a finite codebook for $0,\ldots,L-1$, testing divisibility by $L$ selects only the representation of zero; the unbounded-language lower bound does not apply. Every fixed finite codebook admits a finite lookup converter. Likewise, externally supplying a digit layer, requiring one fixed word length, or forbidding leading-zero padding changes the model. The exact comparison above is $L$ states for padded binary versus $kL^k$ trim states for padded legal $k$-bonacci words; the latter count includes the cost of enforcing legality.

#### 1.3.3 LSD continuation residues

**定义 1.9。** For least-significant-digit reading, let a legal prefix have length $t$, trailing run $a\in\{0,\ldots,k-1\}$, and accumulated residue $r\in\mathbb Z/L\mathbb Z$. Given a terminal residue set $H\subseteq\mathbb Z/L\mathbb Z$, its continuation language is
$$
R_{a,r,t}
=\left\{u:
\begin{array}{l}
u\text{ is legal after the incoming run }a,\\
r+\displaystyle\sum_{i=0}^{|u|-1}u_iG_{t+i}\in H\pmod L
\end{array}
\right\}.
\tag{TM.537}
$$
Let $D_{a,t}$ be the set of increments $\sum_i u_iG_{t+i}\pmod L$ attained by these legal continuations, with no upper bound on $|u|$.

**命题 1.10（pure weight period）。** The sequence $(G_n\bmod L)_{n\ge0}$ is purely periodic. A period $P\le L^k$ can be chosen for its consecutive-weight vectors.

**Proof.** The vector $(G_n,\ldots,G_{n+k-1})$ evolves by
$$
(w_0,\ldots,w_{k-1})
\longmapsto
(w_1,\ldots,w_{k-1},w_0+\cdots+w_{k-1}).
\tag{TM.538}
$$
The companion matrix has determinant $(-1)^{k-1}$, hence is invertible over $\mathbb Z/L\mathbb Z$. It permutes the finite set of $L^k$ weight vectors. Every orbit is therefore periodic from its initial state. $\square$

**命题 1.11（unrestricted attainable residues）。** For every $a,t$,
$$
D_{a,t}=\mathbb Z/L\mathbb Z.
\tag{TM.539}
$$

**Proof.** Let $P$ be the preceding period. Since $G_0=1$,
$$
G_{jP}\equiv1\pmod L\qquad(j\ge0).
\tag{TM.540}
$$
Fix $c\in\{0,\ldots,L-1\}$. Choose $c$ absolute digit positions divisible by $P$, all sufficiently far beyond $t$, with consecutive selected positions separated by a multiple of $P$ at least $k$. Put a $1$ at each selected position and $0$ at every other continuation position. Initial zeros clear the incoming run $a$, and the separation makes the continuation legal. Each selected position contributes $1\pmod L$, so its total increment is $c\pmod L$. For $c=0$, the empty continuation suffices. $\square$

**命题 1.12（residue quotient）。** For fixed $a,t$, two residue labels have identical continuation languages if and only if
$$
R_{a,r,t}=R_{a,r',t}
\quad\Longleftrightarrow\quad
r-r'\in\operatorname{Stab}(H),
\tag{TM.541}
$$
where
$$
\operatorname{Stab}(H)
=\{s\in\mathbb Z/L\mathbb Z:H+s=H\}.
\tag{TM.542}
$$
Consequently the quotient of all residue labels at fixed run and phase has
$$
\frac{L}{|\operatorname{Stab}(H)|}
\tag{TM.543}
$$
classes.

**Proof.** More generally, equality of continuation languages is equivalent to
$$
(H-r)\cap D_{a,t}=(H-r')\cap D_{a,t}.
\tag{TM.544}
$$
Each continuation has a definite increment, and each element of $D_{a,t}$ has a realizing continuation, proving both directions. By unrestricted attainability, the displayed equality reduces to $H-r=H-r'$. This says exactly that $r-r'$ belongs to the translation stabilizer of $H$, which is a subgroup. Its cosets give the stated count. $\square$

**命题 1.13（phase reachability and the finite-layer boundary）。** For any phase $p\pmod P$, run $a$, and residue $r$, a legal LSD prefix realizes $(a,r,p)$ at some sufficiently large length congruent to $p$. At one prescribed finite length, the reachable residues can form a proper subset.

**Proof.** Choose a large length $n\equiv p\pmod P$ and prescribe exactly $a$ final ones, preceded by a zero. Their residue contribution depends only on $a$ and $p$. Correct this contribution to $r$ by placing at most $L-1$ isolated ones at earlier positions divisible by $P$, with gaps at least $k$ and a zero separating them from the final run. Increasing $n$ within its phase supplies enough space without changing the prescribed final contribution. This realizes every label. At the exact layer $n=0$, only run $0$ and residue $0$ are reachable, which proves the finite-layer distinction. $\square$

**注 1.14。** A finite continuation horizon can restrict $D_{a,t}$ and must remain part of the task. The unrestricted residue quotient also supplies no unconditional factor for distinguishable phases: when $H$ is empty or is the whole residue group, the arithmetic phase does not affect acceptance. An autonomous sufficient state is $(a,r,t\bmod P)$; an externally indexed layer can instead supply $t$ and its weights to the transition rule.

#### 1.3.4 Independent growth roots and rational conversion

**文献事实 1.15。** For every $k\ge2$, the polynomial
$$
\psi_k(x)=x^k-x^{k-1}-\cdots-x-1
\tag{TM.545}
$$
is irreducible over $\mathbb Q$ and has exactly one zero outside the unit circle. Its positive zero $\lambda_k$ lies in $(1,2)$. These polynomial facts are stated by Diego Marques in *On the intersection of two distinct k-generalized Fibonacci sequences*, Mathematica Bohemica 137 (2012), 403–413, **printed page 411**, citing D. A. Wolfram, *Solving generalized Fibonacci recurrences*, Fibonacci Quarterly 36 (1998), 129–145. [Marques source](https://mat.unb.br/diego/doc/trifibonacci.pdf), DOI [10.21136/MB.2012.142996](https://doi.org/10.21136/MB.2012.142996).

**命题 1.16（multiplicative independence）。** If $k\ne\ell$, then $\lambda_k$ and $\lambda_\ell$ are multiplicatively independent. Each $\lambda_k$ is also multiplicatively independent of $2$.

**Proof.** For an integer $a>0$, put $\gamma=\lambda_k^a$ and $K=\mathbb Q(\gamma)$. Any $K$-conjugate $\alpha$ of $\lambda_k$ is a $\mathbb Q$-conjugate and satisfies
$$
\alpha^a=\gamma,
\qquad |\alpha|=\lambda_k>1.
\tag{TM.546}
$$
The unique conjugate outside the unit circle is $\lambda_k$, so $\alpha=\lambda_k$. Characteristic-zero separability implies
$$
[\mathbb Q(\lambda_k):K]=1,
\qquad \mathbb Q(\lambda_k^a)=\mathbb Q(\lambda_k).
\tag{TM.547}
$$
If $\lambda_k^a=\lambda_\ell^b$ for positive integers $a,b$, the two fields coincide. Irreducibility gives their degrees as $k$ and $\ell$, hence $k=\ell$.

The monic polynomial $\psi_k$ has constant term $-1$, so $\lambda_k$ is an algebraic unit. An equality $\lambda_k^a=2^b$ with $a,b>0$ would give
$$
N_{\mathbb Q(\lambda_k)/\mathbb Q}(\lambda_k)^a
=2^{bk},
\tag{TM.548}
$$
whose left side is $\pm1$ and whose right side exceeds $1$. This is impossible. Since all numbers considered exceed $1$, every nontrivial multiplicative dependence would yield an equality with positive exponents of one of these forms. $\square$

**定理 1.17（Durand–Rigo, Cobham theorem for Bertrand systems）。** Let $U,V$ be Bertrand numeration systems associated with multiplicatively independent Parry numbers $\alpha,\beta$. A set $X\subseteq\mathbb N$ is recognizable in both systems if and only if it is ultimately periodic. This is Theorem 5.22, printed page 920, of Durand and Rigo, *On Cobham’s theorem*. The association of Bertrand systems with their real-base languages is specified in Theorem 2.2, printed page 901. Recognizability may be expressed using canonical words or their regular leading-zero padding. [Source](https://orbi.uliege.be/bitstream/2268/39461/1/Chapter26.pdf).

**命题 1.18（applicability）。** This theorem applies to two distinct $k$-bonacci systems, and to a $k$-bonacci system and binary.

**Proof.** In the padded-word convention, the Bertrand property is $w\in\mathcal L_k$ if and only if $w0^n\in\mathcal L_k$ for every $n\ge0$. Appending zeros preserves legality, and deleting appended zeros cannot remove an internal forbidden run. Passing between canonical and padded words preserves recognizability. The positive root satisfies
$$
1=\lambda_k^{-1}+\cdots+\lambda_k^{-k}.
\tag{TM.549}
$$
To verify the greedy digits, put $r_j=\sum_{h=1}^{k-j}\lambda_k^{-h}$ for $0\le j\le k$. Then $r_0=1$, $r_k=0$, $0\le r_j<1$ for $j\ge1$, and $\lambda_kr_{j-1}=1+r_j$ for $1\le j\le k$. Thus the greedy expansion of $1$ is $1^k$, and $\lambda_k$ is a simple Parry number. Binary is a Bertrand system associated with the Parry number $2$. The required multiplicative independence is the preceding proposition. $\square$

**命题 1.19（no universal rational converter）。** Let $U,V$ be distinct systems among binary and the $k$-bonacci systems. There is no rational two-tape relation that is total on the canonical $U$-representations of all natural numbers and relates each input only to equal-valued canonical $V$-representations. The conclusion still holds with regular leading-zero padding and with either fixed digit orientation on each tape, independently.

**Proof.** Rational transductions send regular languages to regular languages. In the source system take
$$
X_U=
\begin{cases}
\{2^n:n\ge0\},&U\text{ is binary},\\
\{G_n:n\ge0\},&U\text{ is }k\text{-bonacci}.
\end{cases}
\tag{TM.550}
$$
Its canonical most-significant-digit language is $10^*$. It is infinite and has unbounded successive gaps: this is immediate for powers of $2$, while for sufficiently large $n$ the recurrence gives
$$
G_{n+1}-G_n\ge G_{n-1}\longrightarrow\infty.
\tag{TM.551}
$$
An infinite ultimately periodic set has bounded eventual gaps, so $X_U$ is not ultimately periodic.

If the proposed relation existed, its image on the regular $U$-language of $X_U$ would be a regular $V$-language representing exactly $X_U$. For padded outputs, removing leading zeros gives its canonical language and preserves regularity. Reversing a language also preserves regularity; consequently, for any chosen input or output orientation, reverse the source test language or resulting output language as appropriate. This argument does not require reversing only one tape of the rational relation itself. Thus $X_U$ would be recognizable in both systems, contradicting the cited theorem. The construction of $X_U$ covers both directions, including binary as source. $\square$

**注 1.20。** A fixed periodic predicate $\{n:n\bmod L\in H\}$ is recognizable in each of these systems. The obstruction concerns a single converter for all integers, tested on a nonperiodic source-recognizable set. It neither prevents finite codebook conversion nor supplies a lower bound for a particular finite set of modular survivors.

#### 1.3.6 Return blocks and native prefixes

The generic weighted continuation theorem is in A卷第2.17节. For the arithmetic state $(a,r,t\bmod P)$ of C卷第1.3.3节, take legal digit continuations as tests, terminal observation $\mathbf1_H$ (or the terminal residue itself), raw digit count as duration, and the actual additive resource vector as cost. Legality includes the incoming run and all intermediate transitions. A fixed terminal objective or duration constraint then depends only on the residual task. Value-preserving integer recoding alone supplies none of this test or action contract; the block construction below supplies it explicitly. Cancellation is a hypothesis of that generic theorem, not a hypothesis imposed on every system in volume A.

**命题 1.21（exact block tests with terminal tails）。** Every $w\in\mathcal L_k$ has a unique decomposition
$$
w=b_1\cdots b_m t,
\qquad
b_i\in\{0,10,\ldots,1^{k-1}0\},
\qquad
t\in\{\varepsilon,1,\ldots,1^{k-1}\}.
\tag{TM.559}
$$
For a raw digit system, give block $b$ its composed raw transition, the sum of its raw edge costs, and roof $|b|$. Give each terminal tail its composed terminal transition, additional cost, and duration $|t|$. The resulting block test has exactly the same final state, observation, total cost, and raw duration as the raw word.

**Proof.** Each zero terminates exactly one run of preceding ones, giving the complete blocks; the final run, if present, is the tail. Avoidance of $1^k$ bounds every run by $k-1$, and the zero positions make the decomposition unique. Transition composition and additivity, first across complete blocks and then across the tail, give all four equalities. $\square$

**推论 1.22（scope of block quotient preservation）。** When complete blocks and terminal tails are both retained as continuation tests, expansion gives the common test correspondence required by the continuation-intertwining theorem in A卷第2.17节. Identify concatenation of encoded tests by concatenating their expanded words and taking the unique decomposition again whenever the concatenation is legal. With the composed raw transitions, costs, and roofs, the corresponding quotient is preserved.

**Proof.** Unique decomposition makes expansion a bijection, independent of the starting state. The specified concatenation makes it composition-preserving. Retaining the raw legality condition gives equivalence of the domains of action. The preceding proposition supplies transition intertwining and the required observation, cost, and raw-duration identities; the state map is the identity on the represented raw states. $\square$

**注 1.23。** This corollary does not identify a skeleton that retains only completed blocks with the full raw-prefix system. For $k=2$, $\varepsilon$ and $1$ have the same list of completed blocks, but different raw durations and different values of the terminal observation “the final digit is $1$.” If stopping inside a block is allowed, the unfinished run and its raw state, cost, and duration must remain available, either as state or as an explicit terminal channel. Counting each complete block as one time unit also changes the task; raw time is the sum of the block roofs and the tail duration.

**命题 1.24（bare bijections do not preserve prefix complexity）。** For every integer $n\ge4$, two subsets of $\{0,1\}^{2n}$ can be carried onto one another by a bijection of that universe while having different native continuation complexity: one has at least $2^n$ distinct residuals at its middle cut, while the other has a DFA with $2n+2$ states.

**Proof.** Let
$$
A_n=\{xx:x\in\{0,1\}^n\},
\qquad
B_n=0^n\{0,1\}^n.
\tag{TM.560}
$$
Both have cardinality $2^n$, so a bijection $A_n\to B_n$ extends to a permutation of the whole finite universe. After a length-$n$ prefix $x$ in $A_n$, the only accepting continuation is $x$; distinct prefixes therefore have $2^n$ distinct residuals. A DFA for $B_n$ uses one state for each length $0,\ldots,2n$ and one rejecting sink, requires zero during the first $n$ digits, permits either digit during the last $n$, and rejects every extra digit. $\square$

**注 1.25。** Native prefix completion and recoding represented values are consequently different relations. The results above compare representation tasks under explicit continuation, cost, and clock conventions. They establish neither a complexity classification of the distinct odd covering problem nor the existence or nonexistence of such a covering.

### 1.4 回返块、稀疏分辨率与测度运输

#### 1.4.1 仓内已有供应及本节范围

以下既有结果的来源是固定仓库快照 `85565d32fc6d30521579532de103c92e9f17b824`。

- [BinaryZeckendorfBlockSkeletonCore](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.lean) 已定义回返块 `zero`、`oneZero`，可选终端通道、展开与解码，并有 `decode_expand`、`expandCode_injective` 等声明。[BinaryZeckendorfBlockSkeleton](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/D5/S0/Automata/BinaryZeckendorfBlockSkeleton.lean) 已处理回返骨架与原机器行为的运输。本节不将有限 $0/10$ 分解重新记为成果。
- [SignedSeriesFibres](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/D5/S1/Digit/Infinite/SignedSeriesFibres.lean) 已复用上述回返块，并显式保留原始数字长度 `len`、数字列表和仿射作用。[WindowCylinderPartition](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/D5/S1/Digit/Infinite/WindowCylinderPartition.lean) 对末尾为 $1$ 的黄金窗口补上强制的 $0$，同时保留实际长度与完成后长度的区别。
- [RRO Context Geometry，定理 9.18 及式 (9.18)–(9.20)](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 已定义禁止 $1^k$ 的 $X_k$、增长根 $\lambda_k$ 及从初态 $0$ 出发的 Perron 转移，明确没有把这份根律称作位置平稳律。
- [RRO 主文，定理 33.9–33.10](https://github.com/the-omega-institute/trureturing/blob/85565d32fc6d30521579532de103c92e9f17b824/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md) 已在黄金情形区分初始根律、位置平稳律与最大熵结论，并引用 W. Parry 的经典工作 [*Intrinsic Markov chains* (1964)](https://doi.org/10.1090/S0002-9947-1964-0161372-1)。本节下述权重直接从仓内已给转移公式推导，Parry 原始全文的独立核对不在这里的证据范围内。

本节新增的连接对象是：在回返块坐标中声明稀疏禁柱，将其延拓查询、概率质量与可计算性双向运输回合法数字空间。前置普通数学结果是 C卷第2.9.1节、C卷第2.9.2节、C卷第2.9.3节、C卷第2.9.4节、C卷第2.9.5节、C卷第2.9.6节、C卷第2.9.7节 与 C卷第2.9.8节；这里使用其常数进制 $b_n=k$ 情形。

#### 1.4.2 有锚的无限回返分块与有效同胚

固定

$$
X_k=\{x\in\{0,1\}^{\mathbb N_0}:x\text{ 不含 }1^k\},
\qquad A_k=\{0,1,\ldots,k-1\},
\qquad Y_k=A_k^{\mathbb N_0}.
$$

位置零之前的虚拟状态取连续 $1$ 的数目为零。为 $r\in A_k$ 定义回返块

$$
B(r)=1^r0,\qquad \tau(r)=r+1.
$$

有限码集 $\{0,10,\ldots,1^{k-1}0\}$ 无前缀冲突：若 $r<t$，在第 $r$ 位，短码已经输出 $0$，长码仍输出 $1$。它对合法载体 $X_k$ 完备；它不是对全部二进制串完备的前缀码。

定义拼接映射

$$
\Phi_k:Y_k\longrightarrow X_k,
\qquad
\Phi_k(y)=B(y_0)B(y_1)B(y_2)\cdots.
$$

任意拼接都合法，因为各段连续 $1$ 的长度至多 $k-1$，段间有 $0$。反过来，任意 $x\in X_k$ 在每个长度 $k$ 的连续窗口中都有零，因而有无穷多个零。依次在零后切开，唯一得到 $B(r_0),B(r_1),\ldots$。由此定义逆映射 $\Psi_k$，满足

$$
\Psi_k\Phi_k=\operatorname{id}_{Y_k},
\qquad
\Phi_k\Psi_k=\operatorname{id}_{X_k}.
$$

两向都有明确的有限读取界：

- 前 $N$ 个块符号足以计算前 $N$ 个原始位，因为每块至少长一位。
- 前 $kn$ 个原始位足以找到前 $n$ 个终止零，因而计算前 $n$ 个块符号。

所以 $\Phi_k,\Psi_k$ 是可计算同胚，且对每个点及每个 oracle 都保留可计算性与 Turing 度。这里并没有通过编码消除一个不可计算点的问题。

对长度为 $n$ 的块字 $a=(a_0,\ldots,a_{n-1})$，记

$$
W(a)=B(a_0)\cdots B(a_{n-1}),
\qquad L(a)=\sum_{i<n}(a_i+1).
$$

完整块柱精确对应原始合法柱：

$$
\Phi_k([a]_{\mathrm{block}})
=X_k\cap[W(a)]_{\mathrm{raw}},
\qquad n\le L(a)\le kn.
$$

这里的长度界指完整展开并归档至第 $n$ 个终止零的原始长度，不声称每种观察协议都必须实际读取全部强制位。

##### 1.4.2.1 同一首差尺度下的度量界

在块空间和原始位空间都采用首差距离 $2^{-\text{首差下标}}$。若两个块串 $y,z$ 首次在从零起的块下标 $d$ 不同，它们的前 $d$ 块共同展开长度为 $L_d\in[d,kd]$。差块的 run 长度设为 $r\ne s$，则原始串的首差位置精确等于

$$
J=L_d+\min(r,s),\qquad 0\le\min(r,s)\le k-2.
$$

因此

$$
2^{-(k-2)}d_{\mathrm{block}}(y,z)^k
\le d_{\mathrm{raw}}(\Phi_ky,\Phi_kz)
\le d_{\mathrm{block}}(y,z).
$$

相等点的两边距离均为零，故同样成立。这给出前向 Lipschitz 和逆向指数 $1/k$ 的 Hölder 控制，并未给出等距。比如前一共同块为 $10$、下一块分别为 $0$ 与 $10$ 时，块距离为 $1/2$，原始距离为 $1/4$。

这与 Context Geometry 定理 9.18 的原生维数 $\log\lambda_k/\log2$ 相容；块空间在其原生首差距离下的维数是 $\log k/\log2$。前述 Hölder 运输不要求两种已指定距离的 Hausdorff 维数相等。若前 $d$ 个共同块全长 $k$，下一块分别为 $0$ 和 $10$，则两距离的比为 $2^{-(k-1)d}\to0$，也直接排除了逆映射的统一 Lipschitz 常数。

#### 1.4.3 任意有限窗口需要保留未完成的 run

每个合法有限二进制字 $w$ 唯一写成

$$
w=W(a)1^j,
\qquad a\in A_k^{<\mathbb N},\quad 0\le j<k.
$$

其中 $W(a)$ 包含全部已出现的零，$j$ 是最后一个零之后尚未结束的连续 $1$ 的个数。空字对应 $a$ 为空、$j=0$；只有连续若干个 $1$ 的短串对应 $a$ 为空、$j>0$。

若 $j=0$，则

$$
\Psi_k(X_k\cap[w]_{\mathrm{raw}})=[a]_{\mathrm{block}}.
$$

若 $1\le j<k$，下一块的完整 run 长度还可以是 $j,j+1,\ldots,k-1$，所以

$$
\Psi_k(X_k\cap[w]_{\mathrm{raw}})
=\bigsqcup_{r=j}^{k-1}[ar]_{\mathrm{block}}.
$$

这给出原始有限观察的完整运输式，而不是先替尚未结束的块任选一个结尾。

在 $j=k-1$ 时，下一原始位被合法性强制为零，故相对 $X_k$ 有

$$
[w]_{\mathrm{raw}}\cap X_k=[w0]_{\mathrm{raw}}\cap X_k.
$$

它们作为候选集合相同，但实际记录长度、发生的读取事件及位置权重仍不同。对于 $j<k-1$，补零通常会严格缩小候选集。例如在 $X_3$ 中，前缀 $1$ 允许下一块为 $10$ 或 $110$；直接补成 $10$ 会删去后一种情况。仓内黄金窗口的强制补零规则因此不能不改条件地推广到任意截断 run。

有限档案的精确压缩应至少保留 $(a,j)$，以及协议要求的时间和来源。只存完整块列表 $a$ 会把不同的未完成 run 合并。

#### 1.4.4 一步动力学、回返动力学与原始时钟

令 $S$ 是 $Y_k$ 上删除一个块符号的移位，$\sigma$ 是 $X_k$ 上删除一个原始位的移位。定义回返映射

$$
T(x)=\sigma^{\tau((\Psi_kx)_0)}x.
$$

则

$$
\Phi_kS=T\Phi_k,
\qquad
\Phi_k(S^ny)=\sigma^{L_n(y)}\Phi_k(y),
\qquad
L_n(y)=\sum_{i<n}(y_i+1).
$$

原始时长满足

$$
n\le L_n(y)\le kn,
\qquad
L_{m+n}(y)=L_m(y)+L_n(S^my).
$$

因此块移位是变步长的回返过程。它不等于原始一步移位。例如所有块符号都等于 $1$ 的点在 $S$ 下不动，其原始展开却是 $(10)^\infty$，在 $\sigma$ 下具有周期二。事实上，$S$ 有 $k$ 个不动点，$\sigma$ 在 $X_k$ 上只有 $0^\infty$ 一个不动点，因此这两个指定的一步系统不存在动力学共轭。

原始一步操作仍能精确运输到块坐标，只是得到另一个操作：

$$
D(y_0,y_1,\ldots)=
\begin{cases}
(y_1,y_2,\ldots),&y_0=0,\\
(y_0-1,y_1,y_2,\ldots),&y_0>0.
\end{cases}
$$

直接展开首块可得

$$
\Phi_kD=\sigma\Phi_k.
$$

所以保留原始单位时间时，应使用这个逐位倒计时操作；把它改成每步丢掉整个首块，改变了时钟合同。若要保留过去已经发生的事件，仍需把相应原始档案一起保存，移位本身不负责保留历史。

位置权重同样必须运输。给定任意原始权重序列 $(W_i)_{i\ge0}$，有限字 $w=W(a)1^j$ 的加权值是

$$
\sum_{i<|a|}\sum_{h=0}^{a_i-1}W_{L_i(a)+h}
+\sum_{h=0}^{j-1}W_{L_{|a|}(a)+h},
\qquad
L_i(a)=\sum_{t<i}(a_t+1).
$$

这保持原始位置。对仓内黄金整数取 $W_i=F_{i+2}$，就是通常的 Fibonacci 数位求值；不能将块下标直接代替原始位下标。本节对一般 $k$ 的结论首先是合法字语言的结论，其他 k-bonacci 数值权重须另行指定。

#### 1.4.5 均匀块测度是一项明确的选择

在 $Y_k$ 上取均匀块乘积概率

$$
u_k=\bigotimes_{i\ge0}\operatorname{Unif}(A_k),
\qquad
\rho_k=(\Phi_k)_*u_k.
$$

于是长度 $n$ 的块柱质量为 $k^{-n}$，其原始像 $[W(a)]\cap X_k$ 的质量也是 $k^{-n}$，无论展开长度 $L(a)$ 在 $n$ 到 $kn$ 之间取哪个值。

对C卷第1.4.3节的有限原始窗口，得到统一可计算公式

$$
\rho_k(X_k\cap[W(a)1^j])=
\begin{cases}
k^{-|a|},&j=0,\\
(k-j)k^{-(|a|+1)},&1\le j<k.
\end{cases}
$$

因此这是一份完整、可计算的概率运输。它没有把每个原始位设成独立均匀：例如

$$
\rho_k([0])=\frac1k,
\qquad
\rho_k(\sigma^{-1}[0])=\frac1k+\frac1{k^2},
$$

第二式分别对应首块长度一且下一块也是零块，或首块为 $10$。两式不同，故这份有锚根律不是原始位置移位的平稳律。

也不能把 $\rho_k$ 解释成普通公平二进制概率在 $X_k$ 上的归一化限制。公平源在前 $m$ 个互不交叠的长度 $k$ 区间中均没有全一块的概率为 $(1-2^{-k})^m$，所以它给 $X_k$ 的质量为零。块测度是由明确的生成规则给出的概率律。

#### 1.4.6 稀疏禁块与双向延拓查询

现在只在 $Y_k$ 中声明以下限制：禁柱由可枚举事件流给出，每个正的**块深度**至多一个最终禁柱；允许重复报告同一个禁柱，不允许同深度竞争的两个禁柱，不允许根柱。设

$$
E=Y_k\setminus\bigcup_i[a_i]_{\mathrm{block}},
\qquad
F=\Phi_k(E)\subseteq X_k.
$$

由于完整块柱精确对应原始柱，禁类呈示有效地运输为

$$
F=X_k\setminus\bigcup_i\bigl(X_k\cap[W(a_i)]_{\mathrm{raw}}\bigr).
$$

两边是同一个对象的不同编码，且

$$
M:=u_k(E)=\rho_k(F).
$$

定义块延拓关系 $R_B(a)\iff E\cap[a]_{\mathrm{block}}\ne\varnothing$，原始延拓关系 $R_X(w)\iff F\cap[w]_{\mathrm{raw}}\ne\varnothing$。非法原始字直接给否定答案。对合法字 $w=W(a)1^j$，有双向公式

$$
R_B(a)\iff R_X(W(a)),
$$

$$
R_X(w)\iff
\begin{cases}
R_B(a),&j=0,\\
\displaystyle\bigvee_{r=j}^{k-1}R_B(ar),&1\le j<k.
\end{cases}
$$

这些公式对空串、无完整块的短串和最大 run 都成立。由此 $R_X$ 与 $R_B$ 在已知 $k$ 下均匀 Turing 等价，不需要额外 oracle 来识别切块边界。

在常数进制 $b_n=k$ 上，稀疏尾和为

$$
\sum_{h>n}k^{-h}=\frac{k^{-n}}{k-1}.
$$

所以对 $k\ge3$，每个仍可延伸的深度 $n$ 块柱满足

$$
u_k(E\cap[a])\ge\frac{k-2}{k-1}k^{-n}>0.
$$

最终总质量的 Cauchy 名加上同一事件呈示，可以一致计算局部质量，再以这个已知间隔判定 $R_B$，随后由上述有限并公式判定 $R_X$。反向由最终可延伸深度 $n$ 块柱计数取得近似

$$
A_n=\#\{a\in A_k^n:R_B(a)\}\,k^{-n},
\qquad
0\le A_n-M\le\frac{k^{-n}}{k-1}.
$$

因此，对 $k\ge3$，有呈示统一的双向运输

$$
\text{总质量名}+\text{禁块呈示}
\ \longleftrightarrow\
\text{块延拓关系}
\ \longleftrightarrow\
\text{原始延拓关系}.
$$

反向恢复质量只需延拓关系及已知模型；前向需要保留事件呈示。这里只需要 $k\ge3$，不要求 $k$ 为素数。

当 $k=2$，对每个固定可枚举呈示及每个 oracle $A$，仍有逐点等价

$$
M\text{ 为 }A\text{-可计算}
\iff R_B\text{ 为 }A\text{-可判定}
\iff R_X\text{ 为 }A\text{-可判定},
$$

但不存在对所有呈示统一的“质量名加呈示恢复延拓”算子。有限／余有限规范深度支撑造成的二进制展开歧义允许逐点硬编码，却不能统一选出正确的一种。

统一性失败直接代入C卷第2.8.5节的同一个二进制家族：把该节的二进字母 $0,1$ 解释为块字母，以 $u_2$ 为参考律。具体对应为：无条件禁去 $[0^n1]$（$n\ge1$），并在机器 $e$ 停机时另禁 $[0]$。两种情况下总质量均为 $1/2$，但块柱 $[0]$ 可延伸当且仅当该机器不停机。所有呈示都满足每块深度至多一个禁柱。通过 $\Phi_2$，同一反例位于黄金合法字空间；块字母 $1$ 在那里代表整个回返块 $10$，不能误读成一个原始位。

这些结论来自明确选择的块分辨率、稀疏预算与均匀块概率。可计算同胚本身既没有提高也没有降低单点的可计算度。

#### 1.4.7 “每层一个”不是同胚不变量

原生合法字树按原始位深度分层，在同一深度，不同节点可以分别有一个或两个合法孩子，因此不是球对称树。

更直接的反例是

$$
X_k=[0]_{X_k}\sqcup[10]_{X_k}\sqcup\cdots\sqcup[1^{k-1}0]_{X_k},
$$

其中 $[w]_{X_k}=X_k\cap[w]_{\mathrm{raw}}$。这些首回返柱两两不交并覆盖整个合法空间，所列原始位深度恰为 $1,2,\ldots,k$，每个深度只有一个。

它们运输到块坐标后却是

$$
Y_k=[0]_{\mathrm{block}}\sqcup[1]_{\mathrm{block}}\sqcup\cdots\sqcup[k-1]_{\mathrm{block}},
$$

即同一块深度一的全部 $k$ 个柱，违反每块深度至多一个的预算。特别地，$k=2$ 时原生的 $[0]\cup[10]=X_2$ 已给出最小反例。

反方向也会失效：块字 $(1)$ 与 $(0,0)$ 的深度分别为一和二，但原始展开为 $10$ 与 $00$，两者都长两位。因此每块深度一个的族，也不保证每原始位深度一个。

由此，拓扑同胚、有效双向编码和相同底层集合，都不足以运输这个按层计费的限制。若要保留原始深度预算，应把完整的长度函数 $L(a)$ 带入约束，而不是在新坐标中重新套用“每块深度一个”。此时已不再是先前常数进制定理的原假设。

#### 1.4.8 Perron／Parry 回返权与均匀块权不同

采用仓内已给的唯一根

$$
\sum_{\ell=1}^k\lambda_k^{-\ell}=1,
\qquad 1<\lambda_k<2.
$$

状态 $i\in\{0,\ldots,k-1\}$ 记录已经读到的末尾连续一的个数。令

$$
h_i=\sum_{\ell=1}^{k-i}\lambda_k^{-\ell},\qquad h_0=1.
$$

仓内固定初态零的 Perron 转移为

$$
P(i\xrightarrow{0}0)=\frac{h_0}{\lambda_kh_i},
\qquad
P(i\xrightarrow{1}i+1)=\frac{h_{i+1}}{\lambda_kh_i}\quad(i<k-1),
$$

最后状态只有输出零的转移。沿从零返回零的块 $1^r0$ 相乘，权重望远镜消去，得到

$$
p_r=\Pr(B(r)\mid\text{刚处于状态零})
=\lambda_k^{-(r+1)},\qquad 0\le r<k.
$$

它们的和为一。每个块结束后都回到同一个状态零；对任意有限块字，逐段使用相同转移便得到

$$
\Pr([a_0\cdots a_{n-1}]_{\mathrm{block}})
=\prod_{i<n}p_{a_i}
=\lambda_k^{-L(a)}.
$$

所以固定回返边界后，这份根律对应非均匀 iid 块概率 $(p_r)$。对于每个有限 $k\ge2$，$p_0=\lambda_k^{-1}$ 与 $p_1=\lambda_k^{-2}$ 不相等，故它不是均匀块测度。

更一般地，任意块 iid 权重 $(p_r)$ 对原始窗口 $w=W(a)1^j$ 给出

$$
\Pr([w]_{X_k})
=\left(\prod_{i<|a|}p_{a_i}\right)
\left(\sum_{r=j}^{k-1}p_r\right).
$$

$j=0$ 时最后一因子为一。在上述 Perron 权重下，若 $N=|w|$，则这恰化成仓内的柱公式

$$
\Pr([w]_{X_k})=\lambda_k^{-N}h_j.
$$

这也再次识别了初始律：

$$
\Pr([0])=\lambda_k^{-1},
\qquad
\Pr(\sigma^{-1}[0])=2\lambda_k^{-2}\ne\lambda_k^{-1}.
$$

故固定初态零的根律不平稳。通常称作最大熵 Parry 概率的平稳版本，还要用相应平稳状态分布；在其状态零回返截面上，完整回返块的条件权仍由上述同一个转移矩阵给出。这里不把截面上的回返根律和任意位置开始的平稳原始律混为一体。

块权与原始时长还满足一个有限概率恒等式。对任意块分布 $a_r$，取自然对数，有

$$
D(a\Vert p)
=-H(a)+\left(\sum_r a_r(r+1)\right)\log\lambda_k\ge0.
$$

因此

$$
\frac{H(a)}{\sum_r a_r(r+1)}\le\log\lambda_k,
$$

等号当且仅当 $a=p$。它比较的是每块熵除以平均原始长度，不将一块时间与一位时间视为相同单位。

在非均匀 $(p_r)$ 下，相同块深度的不同柱具有不同质量，因而“规范深度支撑的质量等于同一列深度权重之和”这一前提已经改变。本节不据此宣称它继承C卷第1.4.6节的质量—延拓统一性分类；需要另外证明适用的权重、正间隔或展开唯一性条件。若原问题原本使用 Parry 律，改用均匀块律是在改变概率模型，不能仅称为同一概率的坐标变换。

#### 1.4.9 k 趋于无穷时的空间与概率边界

固定有限 $k$ 时零的间隔有界，整个 $X_k$ 都能解析为无限块。去掉这一统一界后，定义

$$
X_\infty^{\mathrm{return}}
=\{x\in\{0,1\}^{\mathbb N_0}:x\text{ 有无穷多个零}\}.
$$

拼接任意有限长度的块 $1^r0$ 给出

$$
\Phi_\infty:\mathbb N_0^{\mathbb N_0}
\longrightarrow X_\infty^{\mathrm{return}},
$$

它仍有唯一逆解析，并是两边乘积拓扑与子空间拓扑下的可计算同胚。逆算法在其有效域内逐次等待下一个零而终止，但不再有仅由块数 $n$ 决定的原始位读取上界。

这个域不是全部二进制空间。$1^\infty$ 以及任意最终全一的串都没有无限个终止零，因此不在像中。另有

$$
\bigcup_{k\ge2}X_k
\subsetneq X_\infty^{\mathrm{return}}
\subsetneq\{0,1\}^{\mathbb N_0}.
$$

第一处严格包含可由 $10\,110\,1110\cdots$ 见证：它可无限分块，但一的 run 长度无界。无限块字母空间 $\mathbb N_0^{\mathbb N_0}$ 非紧，回返域也不是闭的；没有产生与整个紧二进制空间的这一同胚。

概率极限同样取决于所保留的权重。均匀 $k$ 块测度下，固定 $N\ge1$ 且 $k>N$ 时

$$
\rho_k([1^N])=\frac{k-N}{k}\longrightarrow1.
$$

所以把这些概率都视为完整二进制空间上的概率时，

$$
\rho_k\Longrightarrow\delta_{1^\infty}.
$$

这由有限柱概率收敛推出；有限柱函数一致逼近紧数字空间上的连续函数。极限集中在一个已经离开无限回返解析域的点上。有限字母表上的均匀分布不存在可直接延续到全部自然数字母的归一化均匀版本。

与此不同，Perron 回返权满足固定 $r$ 下

$$
\lambda_k^{-(r+1)}\longrightarrow2^{-(r+1)}.
$$

对固定原始词 $w$，当 $k>|w|$ 时它合法，而 $\lambda_k\to2$ 以及 $h_j=(1-\lambda_k^{-(k-j)})/(\lambda_k-1)\to1$ 给出

$$
\Pr_k^{\mathrm{Perron,root}}([w])
=\lambda_k^{-|w|}h_j\longrightarrow2^{-|w|}.
$$

因此这些有锚根律的原始位极限是公平二进制概率。几何块权 $2^{-(r+1)}$ 在无限字母上归一化，并通过 $\Phi_\infty$ 生成这份概率；缺少无限个零的串在公平二进制概率下是零质量集合。这个满测度的运输不补成全空间拓扑同胚，也不把均匀块极限改成同一个结果。

#### 1.4.10 接口结论与保留义务

可直接接入已有稀疏分辨率理论的对象是

$$
\left(
\text{回返块坐标},\
\text{块深度预算},\
\text{均匀块测度},\
\text{双向有限柱运输}
\right).
$$

在这一明确接口上，$k\ge3$ 有呈示统一的正间隔算法，$k=2$ 保留逐点等价但失去对全部呈示统一的前向算法。原生合法字树、原始位深度预算、Parry 概率及原始单位时间分别需要其运输公式，不能由同胚一并省略。

回返块把一个关系结构改写成完整符号空间；它提供可逆的辅助坐标。究竟保留哪些操作、时长、权重和每层资源，决定后续能合法迁移哪条定理。本节只建立上述具体桥梁，没有把数值解码、其他概率律或无限层极限自动纳入同一结算。

## 2. 有效提升、幸存关系与概率接口

### 2.1 有效幸存提升、分支存在与停机判定的边界

固定有限层的观察可能不足以恢复原对象；这不自动产生不可计算分支，更不自动产生 Gödel 不完备。这里区分三个问题：层与投影是否有效给出，给定合法节点是否总有合法提升，以及整个无限系统是否满足这些前提。对逐步排除一个同余类的幸存塔，严格 LCM 增长实际给出每条纤维的合法提升，因而具有直接可计算的相容分支。其输出首先是指定逆系统的线程，不必是普通整数。

#### 2.1.1 有效满射提升给可计算分支

令 $H_n\subseteq\mathbb N$ 以自然数编码节点，成员可统一有效枚举，且每层非空。令 $\pi_n:H_{n+1}\to H_n$ 在合法输入上统一可计算，并满足

$$
\forall n\ \forall x\in H_n\ \exists y\in H_{n+1}:\ \pi_n(y)=x.
\tag{TM.464}
$$

节点相等可判定；“可计算投影”包含对每个合法输入终止的保证。有限非空集合是本命题的一个适用情形。

**命题 2.1。** 存在可计算函数 $b:\mathbb N\to\mathbb N$，使

$$
b(n)\in H_n,\qquad \pi_n(b(n+1))=b(n)\quad\text{对所有 }n.
\tag{TM.465}
$$

**证明。** 枚举 $H_0$，取首次出现的成员为 $b(0)$。已得 $b(n)$ 后，枚举 $H_{n+1}$，逐个计算 $\pi_n(y)$，遇到 $\pi_n(y)=b(n)$ 的第一个成员就取为 $b(n+1)$。式(TM.464)保证搜索终止。归纳保证每次输出合法且相容；为计算 $b(n)$ 只需有限次这样的终止搜索，因此 $b$ 可计算。这里不必先判定整座塔的非空与满射承诺是否为真。证毕。

如果有限集由可完成的完整列表给出，或在可计算有限候选域中有可判定成员关系，可直接取最小合法提升。若“有效可枚举有限集”仅指 uniformly c.e.，则应写“首个找到的提升”，不能无条件写“数值最小的提升”。例如

$$
F_e=\{1\}\cup\bigl(\{0\}\text{ 若程序 }e\text{ 停机，否则 }\varnothing\bigr)
\tag{TM.466}
$$

是一族统一可枚举、非空有限集；若可由 $e$ 统一算出 $\min F_e$，便能判定停机。搜索首个成员则可始终输出先枚举的 $1$。上述分支构造不依赖枚举完成信号，也不承诺统一时间复杂度。

#### 2.1.2 递归二叉树的无死路条件

令 $T\subseteq\{0,1\}^{<\mathbb N}$ 是前缀封闭且成员关系可判定的二叉树，令 $H_n=T\cap\{0,1\}^n$，投影删去最后一位。每层可通过枚举全部 $2^n$ 个字得到完整有限列表。

若根存在且每个节点至少有一个直接子节点在 $T$ 中，则投影 $H_{n+1}\to H_n$ 对每层满射。于是式(TM.465)给可计算分支；更直接地，当前节点的 $0$ 子节点若合法就选它，否则选合法的 $1$ 子节点。

因此，一个无限递归二叉树若没有可计算无限分支，就不可能同时是处处无死路的树。这里不是缺少一份无死路证明才无法选取：该全局无死路性质本身与“无可计算分支”不相容。“每层非空”仅保证存在任意深的节点，不保证每个已选节点都能继续。

将树剪到全部可无限延伸节点后，所得非空树确实无死路。但若原树没有可计算分支，这份剪枝结果便不能仍以统一可枚举节点和可计算前缀投影给出，否则C卷第2.1.1节再次产生可计算分支。有效取得无限延伸核心是额外信息，不能由原树的递归成员关系免费得到。

本节这里给的是关于任何满足相应条件之树的条件推论；没有重新构造一棵 Kleene 树，也没有把“Kleene 最小不动点定理”当作该树存在定理。

#### 2.1.3 同余幸存塔的纤维数和显式提升

给定可计算的整数相位 $a_i$ 与正模数 $m_i$，$i\ge1$。定义

$$
L_0=1,\qquad L_n=\operatorname{lcm}(m_1,\ldots,m_n),\qquad
H_n=\{h\in\mathbb Z/L_n\mathbb Z:\;
 h\not\equiv a_i\pmod{m_i}\ (1\le i\le n)\}.
\tag{TM.467}
$$

$H_0$ 为唯一零剩余类。采用 $0\le h<L_n$ 的标准整数代表后，各 $H_n$ 是可完成的可计算有限列表，投影是模 $L_n$ 约化。

设旧 $L=L_n$，新模数 $m=m_{n+1}$，相位 $a=a_{n+1}$，并令 $d=\gcd(L,m)$、$L'=\operatorname{lcm}(L,m)$、$q=L'/L=m/d$。旧幸存类 $h$ 的全部新层提升是 $h+jL$，$0\le j<q$。旧约束在全部提升上继续成立，新约束排除的提升满足

$$
h+jL\equiv a\pmod m
\ \Longleftrightarrow\
(L/d)j\equiv(a-h)/d\pmod q
\quad\text{在 }h\equiv a\pmod d\text{ 时}.
\tag{TM.468}
$$

若 $h\not\equiv a\pmod d$ 无解；否则 $\gcd(L/d,q)=1$，解在模 $q$ 下恰有一个。因此这是C卷第1.1节同一纤维计数的直接应用：

$$
|\{y\in H_{n+1}:y\bmod L_n=h\}|
=q-\mathbf1_{\{h\equiv a_{n+1}\pmod{\gcd(L_n,m_{n+1})}\}}.
\tag{TM.469}
$$

若每一步严格 LCM 增长，即 $q>1$，则每条旧幸存纤维至少有 $q-1\ge1$ 个新幸存者。故全部限制投影满射，从 $H_0\ne\varnothing$ 归纳得到所有 $H_n\ne\varnothing$。这里没有把不同旧状态各自可达的提升拼成不相容的实现。

甚至无需枚举整层。取 $h_0=0$，逐次定义

$$
h_{n+1}=
\begin{cases}
h_n,&h_n\not\equiv a_{n+1}\pmod{m_{n+1}},\\
h_n+L_n,&h_n\equiv a_{n+1}\pmod{m_{n+1}}.
\end{cases}
\tag{TM.470}
$$

第二种情形中，若 $h_n+L_n$ 也被排除，就有 $m_{n+1}\mid L_n$，与 $q>1$ 矛盾。又 $h_n+L_n<2L_n\le L_{n+1}$，故结果仍是标准代表；它保持旧剩余类并避开新类。归纳得到一条可计算相容幸存线程。这也恰是该纤维标准代表中的最小合法提升，因为 $j=0$ 失败时 $j=1$ 已成功。

特别地，逐步只排除一个同余类且每步严格增长的这类系统，不发生任何有限层消亡，不能在保持这些假设的同时将停机编码为首次有限消亡。

#### 2.1.4 线程属于哪一种完成对象

上述算法首先给出

$$
(h_n)_n\in\varprojlim_n H_n
\subseteq\varprojlim_n\mathbb Z/L_n\mathbb Z.
\tag{TM.471}
$$

后一个空间是指定模数链的完成对象。仅有 $L_n\to\infty$ 或每步严格整除，不保证它就是完整的 $\widehat{\mathbb Z}$。在标准剩余类识别下，若每个正整数都整除某个 $L_n$，该链对全部模数共尾，才由限制与相容提升得到完整 profinite 接口；例如 $L_n=2^n$ 给 $\mathbb Z_2$，它漏掉其他素数方向。

可计算线程也不必由一个普通整数实现。给一个明确例子：可计算枚举全部整数为 $z_1,z_2,\ldots$，取 $m_i=2^i$、$a_i=z_i$。每步 LCM 严格翻倍，所以式(TM.470)产生一条可计算二进整数幸存线程。但

$$
\bigcup_{i\ge1}(z_i+2^i\mathbb Z)=\mathbb Z,
\tag{TM.472}
$$

因为每个 $z_i$ 在自己的类中。故没有普通整数能实现这个幸存线程。有限层共同实现、无限相容线程及原整数实现是不同结论。

#### 2.1.5 环境分辨率增长不保证限制投影满射

即使环境 $Q_n=\mathbb Z/2^n\mathbb Z$ 每步严格细化，其非空合法子集也可能丢失旧节点。例如在第1层取 $H_1=\{0,1\}\subseteq\mathbb Z/2\mathbb Z$，以后取 $H_n=\{0\}\subseteq\mathbb Z/2^n\mathbb Z$；投影 $H_2\to H_1$ 漏掉 $1$。环境满射未传给合法子集。

更一般地，将二叉字 $s_0\cdots s_{n-1}$ 编为 $\sum_{j<n}s_j2^j\bmod2^n$，就把任意递归二叉树的各层放入这条严格细化的环境塔。约化恰对应前缀截断。因而一个没有可计算分支的无限递归二叉树，也可住在严格增长的二进制环境中；问题出在限制后的幸存投影，不在环境模数是否变大。

这与C卷第2.1.3节并不矛盾：C卷第2.1.3节额外要求每步由一条实际新同余类排除，并由其精确纤维计数证明满射。任意树的合法子集不自动具有这份结构。

#### 2.1.6 HALT 模型区分存在判定和承诺下的选取

对程序编号 $e$，令

$$
Q_n=\mathbb Z/2^n\mathbb Z,\qquad
H_n(e)=
\begin{cases}
Q_n,&e\text{ 在前 }n\text{ 步内尚未停机},\\
\varnothing,&e\text{ 已在前 }n\text{ 步内停机}.
\end{cases}
\tag{TM.473}
$$

每个有限层可由有界模拟计算。限制投影总有定义：新层非空意味着旧层非空；空新层只有空域映射。若机器不停止，各层都为 $Q_n$，常零线程可计算；若机器停机，某层起为空，不存在线程。因此

$$
\varprojlim_nH_n(e)\ne\varnothing
\quad\Longleftrightarrow\quad
e\text{ 不停机}.
\tag{TM.474}
$$

存在性不能由 $e$ 总可计算地判定，否则可判定停机。但在“不停机、故所有层非空”的承诺下，同一个算法对所有输入都输出常零坐标，就已提供合法分支；它无须先验证承诺。

停机实例在首次清空处破坏非空满射前提，所以这个模型不是C卷第2.1.1节的反例。它也不满足C卷第2.1.3节严格增长、单条新同余类精确排除的全部结构：后者不允许把整层突然清空。环境仍严格细化，并不能消除这种区别。

因此“判定是否存在分支”和“在有效满射等承诺下计算一条分支”有不同量词。无可计算分支的递归树则显示：仅知道非空，也不自动给一个选取算法。

#### 2.1.7 到有限覆盖和 Gödel 还缺哪一条桥

一个已经给出的有限同余类族是否覆盖全部整数，可有限判定：令 $L$ 为模数 LCM，只需检查

$$
\forall r\in\{0,\ldots,L-1\}\ \exists i:\ r\equiv a_i\pmod{m_i}.
\tag{TM.475}
$$

所以不存在把任意程序通过总可计算变换送到一份明确有限族、并让这份族的覆盖真假等价于停机的归约；否则有限 LCM 检查就判定停机。若改成搜索无界规模的有限见证族，或改成无限有效生成的约束系统，那是另一种输入与量词，必须重新证明归约。

对有限互异奇数模数覆盖目标，严格 LCM 增长只是一个受限子类。互异奇数 $3,5,15$ 已说明互异与奇性不保证每一步增长；最后一个模数不增加已有 LCM。由式(TM.469)，若某层是首次有限消亡，其前层非空，则该步必须 $q=1$。当前论证排除了“全程严格增长仍有限消亡”，没有处理全部允许的不增分辨率约束层，因此不解决该覆盖目标。

Gödel 不完备还要求指定形式系统及适当的一致性、有效公理化和表达能力前提。有限观察不充分、完成线程不属于原载体、HALT 存在判定不可计算、指定形式系统内的不可证明性，不能仅由“都有无限过程”互相推出。要把某个具体覆盖命题接到不可判定或独立性结论，须给保留有限性、模数限制、共同实现和结论方向的实际归约或证明；这里没有这样的结算。

#### 2.1.8 固定快照中的直接所有者与来源范围

下列 Lean 声明的来源定位为不可变快照 237012b49d0d4729a86f7e9dd252d94df1de8dd0。它们作为已有数学接口使用；本节不新增对应 Lean 声明或形式核验。

- D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.lean 的 finite_cofiltered_limit_nonempty：余滤图式的对象逐个有限且非空，即有相容 section。它直接调用 Mathlib 的 nonempty_sections_of_finite_cofiltered_system。其存在结论不要求这里逐层满射，但也没有提供算法可计算性；不能把非空声明改报为可计算选择。
- D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean 的 stateThread_bijective_iff_complete_and_separates：原状态到线程的映射双射，当且仅当线程完备且分离状态。其 ThreadComplete 明确要求所有线程由原状态实现，直接承担C卷第2.1.4节不可省略的桥；stateEquivInverseLimit 在源码中是 noncomputable 定义，不构成本节算法的已有实现。
- D5/S0/Computability/ClosureUndecidable.lean 的 closure_reading_unreachable：对代码行为外延不变且非平凡的闭合谓词，调用 Mathlib 的 ComputablePred.rice₂ 得不可计算判定；empty_ledger_reading_unreachable 是具体实例。其前件不能从“名字叫闭合”或“分辨率严格增长”取得。
- D5/S0/Computability/FiniteCounterexampleCertificate.lean 的 finite_readout_counterexample_certificate：一个 Boolean 全称有限读数失败，当且仅当有有界搜索找到的反例证书。它承担有限拒绝证据接口，不给无限承诺的统一决定程序。
- D5/S1/FixedPoints/KleeneStageLimit.lean 的 inductive_definition_is_supremum_of_stages：$\omega$-Scott 连续序自映射的最小不动点是有限迭代的上确界。它是 Kleene 最小不动点定理，不能作为“递归二叉树存在但无可计算分支”的所有者。
- D5/S0/Computability/Searchability/SearchableWindowDecision.lean 的 searchable_window_forall_decidable：在已供应满足相应完备性的 Boolean 选择器时，得到全称测试的判定。它将选择器列为前提，不自动从有限层非空制造这种选择器。

这里的仓内来源范围限于上述固定快照及列明的 D5 接口；这些接口不提供一般有效满射逆系统的可计算分支定理或 recursive binary Kleene tree 的存在定理。这不声称该快照其他位置、第三方库或文献不存在对应结果。本节的有效提升短证、CRT 纤维复用和具体 HALT 模型属于普通数学连接，不取得新增 Lean 或原创性名义。

### 2.2 奇素数幂对角幸存集：正测度、有效有限层与不可计算线程

存在一个由互异三幂模数的同余类有效枚举而成的无限约束族，其三进整数幸存集具有至少 $1/2$ 的 Haar 测度，却不含任何可计算点。每个有限模拟层均可完整计算，环境模数与候选幸存者数量还可以每步严格增长。由这些有限层组成的相容无限线程确实存在，但没有可计算线程。

关键区别是：有限模拟层中的候选节点，不全是最终幸存集的精确投影；被延迟发现的约束会删掉一些旧候选。若改用按停机事件逐条加入约束的实际最小公倍数塔，则非满射步骤有无限多个，而且它们全部发生在实际最小公倍数不增长的平台上。两种呈现描述同一个最终幸存集，却不能交换各自的单步假设。

#### 2.2.1 三进整数、有效坐标与对角约束

以有限剩余类的逆极限定义三进整数空间：

$$
\mathbb Z_3=\varprojlim_{n\ge0}Q_n,
\qquad
Q_n=\mathbb Z/3^n\mathbb Z,
\qquad
\rho_n:Q_{n+1}\longrightarrow Q_n.
\tag{TM.476}
$$

这里 $Q_0$ 是单点集，$\rho_n$ 为模 $3^n$ 约化。用 $0,\ldots,3^n-1$ 作为 $Q_n$ 的标准代表，并记 $q_n(x)$ 为 $x$ 的第 $n$ 层标准剩余类。一个 $x\in\mathbb Z_3$ 称为可计算，当且仅当函数 $n\mapsto q_n(x)$ 是总可计算函数。这等价于其三进位序列可计算：有限求和给剩余类，相邻剩余类的差给下一位。

固定一个标准的、覆盖所有部分可计算函数的有效程序枚举

$$
\varphi_e:\mathbb N\rightharpoonup\mathbb N,
\qquad
D=\{e\in\mathbb N:\varphi_e(e+1)\downarrow\}.
\tag{TM.477}
$$

当且仅当 $\varphi_e(e+1)$ 停机时，记输出为 $a_e$，枚举一条禁用同余类及其三进柱集：

$$
a_e+3^{e+1}\mathbb Z,
\qquad
C_e=\{x\in\mathbb Z_3:q_{e+1}(x)\equiv a_e\pmod{3^{e+1}}\}.
\tag{TM.478}
$$

输出 $a_e$ 可为任意自然数，使用时约化到标准代表。每个 $e$ 最多发出一次约束，因此禁用模数全都大于 $1$、为奇数、互不相同，且只含素因子 $3$。程序枚举可以有不同代码计算同一个函数；这不破坏模数互异，因为模数由代码编号 $e$ 决定。

令

$$
U=\bigcup_{e\in D}C_e,
\qquad
K=\mathbb Z_3\setminus U.
\tag{TM.479}
$$

有效枚举的具体实现为：在计算阶段 $s\ge1$，分别对所有 $e<s$ 的输入 $e+1$ 模拟 $s$ 步，输出此前尚未发出的已停机事件；同阶段内按编号递增排列。每一阶段都是有限运算，每一实际停机计算终将被发现，未停机者从不发出约束。记 $K_s$ 为完成计算阶段 $s$ 后排除全部已见禁柱所得的集合，$K_0=\mathbb Z_3$。阶段 $s$ 只含深度至多 $s$ 的已见约束，故 $K_s$ 是可计算的既开又闭集，并有 $K_{s+1}\subseteq K_s$、$\bigcap_sK_s=K$。后文的有界候选 $H_n$ 特指在阶段 $s=n$ 读取深度 $n$ 的对角选择，$q_n^{-1}(H_n)=K_n$；任意阶段与任意深度仍可分别查询。实际逐事件 LCM 塔另以事件计数 $j$ 索引，其分辨率为 $L_j=3^{M_j}$。这一算法给出 $U$ 的柱集枚举，所以 $U$ 有效开，$K$ 有效闭；在三进位空间中，$K$ 是一个 $\Pi^0_1$ 类。

#### 2.2.2 正测度、无可计算点及整数覆盖

令 $\mu$ 为 $\mathbb Z_3$ 的 Haar 概率测度。模 $3^r$ 的每个柱集测度为 $3^{-r}$，因而

$$
\mu(U)
\le\sum_{e\in D}3^{-(e+1)}
\le\sum_{e\ge0}3^{-(e+1)}
=\frac12,
\qquad
\mu(K)\ge\frac12.
\tag{TM.480}
$$

这里只用可数次可加性所给的并集上界，不要求不同柱集独立或互不相交。特别地，$K$ 非空。

**命题 2.2。** $K$ 不含可计算的三进整数。

**证明。** 假设 $x\in K$ 可计算，令 $g(n)=q_n(x)$。这是总可计算函数，故存在程序编号 $e$ 使 $\varphi_e=g$。于是 $\varphi_e(e+1)$ 停机并输出 $q_{e+1}(x)$，因此 $e\in D$ 且 $x\in C_e$，与 $x\in K$ 矛盾。证毕。

每个普通整数 $z\in\mathbb Z$ 都有可计算的标准剩余类函数 $n\mapsto z\bmod3^n$，负整数亦然。因此

$$
K\cap\mathbb Z=\varnothing,
\qquad
\bigcup_{e\in D}\bigl(a_e+3^{e+1}\mathbb Z\bigr)=\mathbb Z.
\tag{TM.481}
$$

这里通过标准嵌入将 $\mathbb Z$ 视为 $\mathbb Z_3$ 的子集。式(TM.480)和式(TM.481)不矛盾：普通整数是一个稠密可数子集，而剩余的三进整数仍可有正测度。

**命题 2.3。** 任意有限子族的禁用类都不能覆盖 $\mathbb Z_3$，也不能覆盖 $\mathbb Z$。

**证明。** 对有限 $F\subseteq D$，

$$
\mu\left(\mathbb Z_3\setminus\bigcup_{e\in F}C_e\right)
\ge1-\sum_{e\in F}3^{-(e+1)}
>\frac12.
\tag{TM.482}
$$

若 $F$ 非空，令 $M=\max_{e\in F}(e+1)$。有限并集是模 $3^M$ 的剩余类之并，正测度的补集至少包含一个模 $3^M$ 的剩余类。取该类的标准整数代表，便得到一个未被有限子族覆盖的普通整数。$F$ 为空时结论直接成立。证毕。

因此，这是一份无限有效呈现的整数覆盖，其每个有限子族都不是覆盖；它不构成有限互异奇数模数覆盖问题的解答。

#### 2.2.3 统一可判定且数量严格增长的有限候选塔

记 $t_e$ 为 $\varphi_e(e+1)$ 的停机步数；未停机时记为 $\infty$。定义第 $n$ 层候选集

$$
H_n=
\left\{h\in\{0,\ldots,3^n-1\}:
\ \forall e<n,\
t_e\le n\Longrightarrow
h\not\equiv a_e\pmod{3^{e+1}}
\right\}.
\tag{TM.483}
$$

对输入 $(n,h)$，只需检查 $0\le h<3^n$，并将有限多个计算各模拟 $n$ 步，即可判定 $h\in H_n$。枚举有限环境中的全部 $h$ 还给出每层可完成的完整列表；这一事实强于仅知道各层可枚举。

所有在阶段 $n$ 已发现的约束在阶段 $n+1$ 仍存在。若 $h'\in H_{n+1}$，其模 $3^n$ 约化也避开所有旧约束。因此约化限制为统一可计算映射

$$
\pi_n:H_{n+1}\longrightarrow H_n,
\qquad
\pi_n(h')=h'\bmod3^n.
\tag{TM.484}
$$

这里尚未断言 $\pi_n$ 满射。

**命题 2.4。** 每层至少保留一半以上的环境节点，而且候选数量逐层严格增长：

$$
|H_n|
\ge 3^n-\sum_{e<n}3^{n-e-1}
=\frac{3^n+1}{2},
\qquad
|H_{n+1}|>3^n\ge|H_n|.
\tag{TM.485}
$$

**证明。** 任意单个 $e<n$ 的约束至多从 $Q_n$ 中删去 $3^{n-e-1}$ 个节点；未发现的约束不删除节点。把所有这些可能删除数相加是一个上界，即使多个约束重叠也成立。有限几何级数给第一式。对下一层应用同一式，

$$
|H_{n+1}|
\ge\frac{3^{n+1}+1}{2}
>3^n.
\tag{TM.486}
$$

$n=0$ 时空约束集给 $H_0=\{0\}$，公式仍成立。证毕。

所以，环境分辨率每步严格提高，实际有限候选数量也每步严格增加。然而，总数增加不保证每个旧节点留下后继；新节点可以集中到另一些旧纤维中。

**命题 2.5。** 通过式(TM.476)的标准坐标识别，有

$$
K=\varprojlim_n H_n.
\tag{TM.487}
$$

**证明。** 若 $x\in K$，它避开所有已发出约束，故每个 $q_n(x)\in H_n$，坐标又天然相容。

反过来，令 $(h_n)_n$ 为 $H_n$ 中的相容线程。由 $\mathbb Z_3$ 的定义，它给出唯一 $x\in\mathbb Z_3$。对任意 $e\in D$，取 $n\ge\max(e+1,t_e)$，则 $H_n$ 已实施第 $e$ 条约束，所以 $h_n\not\equiv a_e\pmod{3^{e+1}}$。相容性给 $x\notin C_e$。这对每个 $e\in D$ 都成立，因此 $x\in K$。证毕。

若线程坐标 $n\mapsto h_n$ 可计算，所对应的 $x$ 便是一个可计算三进整数，与C卷命题2.2 矛盾。故这是一个层成员关系统一可判定、每层有限非空、层大小每步严格增长、逆极限非空，却没有可计算相容线程的逆系统。按低位三进数字解释 $h_n$，它也给出一棵递归三叉树：删去最后一位即为式(TM.484)，各层大小满足式(TM.485)。

#### 2.2.4 候选层与最终幸存集的精确投影

定义最终幸存集的真实有限观察像

$$
R_n=q_n(K).
\qquad
R_n\subseteq H_n\subseteq Q_n.
\tag{TM.488}
$$

两类有限集承担不同结论。$H_n$ 只排除了阶段 $n$ 已发现的冲突，故其中可以有以后被排除、无法延伸成无限线程的节点。$R_n$ 则只保留确实属于某个最终幸存点的坐标。不能将式(TM.485)中的候选增长当成每个候选节点均可全局实现的证书。

精确投影间的约化

$$
\rho_n|_{R_{n+1}}:R_{n+1}\longrightarrow R_n
\tag{TM.489}
$$

必定满射：对任意 $r\in R_n$，按定义存在同一个实际点 $x\in K$ 满足 $q_n(x)=r$，其 $q_{n+1}(x)$ 就是合法提升。这个论证使用同一个 $x$，没有把不同对象的分别可达坐标拼接起来。

**命题 2.6。** 不存在 $R_n$ 的统一有效枚举。因此也不存在其统一可计算完整有限列表。

**证明。** 若存在统一枚举，先从非空 $R_0$ 取首个枚举到的节点。已取到 $r_n\in R_n$ 后，枚举 $R_{n+1}$，对每个枚举到的节点计算模 $3^n$ 的约化，取首个约化为 $r_n$ 的节点。式(TM.489)的满射性保证每次搜索终止。这样得到总可计算的相容坐标序列；由 $R_n\subseteq H_n$ 与C卷命题2.5，它对应 $K$ 中的可计算点，矛盾。证毕。

这里否定的是以 $n$ 为输入的统一有效枚举；每个单独固定的有限 $R_n$ 仍有有限列表。证明只需“首个枚举到的提升”，不需要从可能没有完成信号的可枚举有限集中计算数值最小元。由于 $H_n$ 具有完整可计算列表，而 $R_n$ 不能统一有效枚举，两者不可能对全部 $n$ 相等。

同时，C卷命题2.5 确实保证：每条完整的候选无限线程都由一个实际 $x\in K$ 实现。这一线程完备性不等于“每个单独候选节点均可延伸”。缺失的是对无限可延伸核心的有效取得，而非环境坐标是否真实存在。

#### 2.2.5 按事件逐条加入的实际 LCM 塔

按C卷第2.2.1节的有效顺序，将所有实际停机事件写成

$$
(e_1,a_{e_1}),(e_2,a_{e_2}),\ldots,
\qquad
m_i=3^{e_i+1}.
\tag{TM.490}
$$

每次仅计一个新事件；同一有限模拟阶段发现多个事件时，它们仍分别占据多个连续事件编号。

这个序列确有无限多项。对每个 $c\in\mathbb N$，常值函数 $n\mapsto c$ 是总可计算函数。不同常值函数必须拥有不同程序编号，而这些编号全部属于 $D$。故 $D$ 无限，无需使用代码填充定理。由有效枚举直到第 $j$ 个事件出现即可计算该事件，而且这种等待对每个固定 $j$ 都终止。

定义

$$
M_0=0,\quad L_0=1,\qquad
M_j=\max_{1\le i\le j}(e_i+1),\quad
L_j=\operatorname{lcm}(m_1,\ldots,m_j)=3^{M_j},
\tag{TM.491}
$$

以及

$$
S_j=
\left\{h\in\{0,\ldots,L_j-1\}:
h\not\equiv a_{e_i}\pmod{m_i}\quad(1\le i\le j)
\right\}.
\tag{TM.492}
$$

每个 $S_j$ 可统一给出完整有限列表，C卷命题2.3 保证它非空。实际 LCM 满足 $L_j\mid L_{j+1}$，模 $L_j$ 约化给出限制映射 $\sigma_j:S_{j+1}\to S_j$。由于 $D$ 无限而自然数的有界子集有限，$M_j\to\infty$；这条实际模数链对全部三幂共尾。

**命题 2.7。** 按共尾坐标识别，$\varprojlim_jS_j=K$，且该事件塔没有可计算线程。

**证明。** $x\in K$ 的模 $L_j$ 坐标避开前 $j$ 个约束，给出相容线程。反之，相容线程因 $M_j\to\infty$ 而给出每个三幂模数上的唯一相容坐标，从而决定一个 $x\in\mathbb Z_3$。第 $i$ 个约束在所有 $j\ge i$ 的层中存在，因此该 $x$ 避开所有 $C_e$，属于 $K$。

若 $j\mapsto h_j\in S_j$ 是总可计算相容线程，则对输入 $n$，有效搜索第一个满足 $M_j\ge n$ 的事件阶段 $j$。这个搜索终止；输出 $h_j\bmod3^n$ 就计算了对应 $x$ 的第 $n$ 层坐标。于是 $x$ 可计算，与C卷命题2.2 矛盾。证毕。

**命题 2.8。** $\sigma_j$ 不满射的步骤有无限多个，而且每个这样的步骤都有 $L_{j+1}=L_j$。

**证明。** 先看单步。设 $L=L_j$，新模数为 $m=m_{j+1}$，$L'=L_{j+1}$。因为二者均为三幂，若 $L'>L$，则 $L'=m$ 且 $q=L'/L$ 是大于 $1$ 的三幂。每个旧幸存者 $h\in S_j$ 在新环境中的全部提升为

$$
h+\ell L,\qquad 0\le\ell<q.
\tag{TM.493}
$$

旧约束在全部这些提升上继续成立。新约束在新环境 $\mathbb Z/L'\mathbb Z$ 中仅禁一个节点，故只在 $h\equiv a_{e_{j+1}}\pmod L$ 的纤维中删除恰好一个提升；其他纤维不受影响。因此

$$
|\sigma_j^{-1}(h)|
=q-\mathbf1_{\{h\equiv a_{e_{j+1}}\pmod L\}}
\ge q-1\ge1.
\tag{TM.494}
$$

故严格实际 LCM 增长的单事件步骤一定满射。不满射只能发生在 $L'=L$。此时新模数整除旧 LCM，映射是有限集合的包含 $S_{j+1}\subseteq S_j$；不满射恰表示至少删掉一个旧幸存者。

再假设只有有限多个不满射步骤。则存在一个固定有限 $j_0$，使所有 $j\ge j_0$ 的 $\sigma_j$ 满射。将这一有限整数 $j_0$ 写入程序，在非空且具有完整可计算列表的 $S_{j_0}$ 中取最小元。之后逐层枚举完整列表，选择约化为当前节点的最小提升；满射性保证每步都能完成。$j<j_0$ 的坐标从所选 $S_{j_0}$ 节点向下约化得到。于是存在一条完整可计算事件线程，违反C卷命题2.7。因此不满射步骤必定无限多。证毕。

论证只用“存在某个有限 $j_0$”推出“存在一份含这个有限常量的可计算程序”，不要求从任意塔有效识别最后一次不满射的位置。这足以与“没有任何可计算线程”矛盾，并未给任意输入塔承诺一个统一找出 $j_0$ 的算法。

同一最终满射推理也说明，有界模拟塔的 $\pi_n$ 必定有无限多个不满射步骤。区别在于：$H_n$ 的环境固定从 $3^n$ 增到 $3^{n+1}$，一个阶段可加入多条延迟发现的约束，所以对它不能套用“每步只加入一条约束”的式(TM.494)。

#### 2.2.6 平台算例、有效排序与严格增长边界

一个有限算例可直接展示实际 LCM 平台如何删除旧节点。先禁用 $0\bmod9$，再禁用 $1\bmod3$。第一步的实际 LCM 为 $9$，标准幸存者为

$$
S_1=\{1,2,3,4,5,6,7,8\}.
\tag{TM.495}
$$

第二步实际 LCM 仍为 $9$，并删去 $1,4,7$，得到

$$
S_2=\{2,3,5,6,8\}\subsetneq S_1.
\tag{TM.496}
$$

两条模数都是互异奇数；不满射来自第二条约束在已有分辨率上实际删去旧节点。这个算例只说明同余类的单步结构，不指定所固定通用程序枚举的前两个事件。

在无限构造中，不能通过“把实际停机编号按大小排好”得到一个总可计算的严格递增事件顺序。理由如下。

**命题 2.9。** $D$ 可枚举但不可判定；它没有总可计算的严格递增枚举。

**证明。** 可枚举性已由C卷第2.2.1节给出。若 $D$ 可判定，则以下部分函数可计算：令 $f(0)=0$；对 $n\ge1$，当 $n-1\in D$ 时永久运行，否则输出 $0$。取程序编号 $e$ 使 $\varphi_e=f$。于是

$$
e\in D
\ \Longleftrightarrow\
f(e+1)\downarrow
\ \Longleftrightarrow\
e\notin D,
\tag{TM.497}
$$

矛盾。若无限 $D$ 有值域恰为 $D$ 的总可计算严格递增枚举，则对输入 $e$，持续计算枚举直到出现某个值至少为 $e$；无限严格递增保证终止，比较是否等于 $e$ 即判定成员关系，再次矛盾。证毕。

因此，按自然数大小排序的非有效约束序列，不能替代C卷第2.2.5节的有效事件呈现来启动可计算贪心提升。严格 LCM 增长的单事件有效塔确实允许逐步计算合法提升；本例的有效事件塔有无限多个真正删除节点的平台，恰好不满足该前提。

有界模拟塔则同时具有严格环境增长和严格候选数量增长，但不具有逐步满射。这说明三个条件各自不同：环境分辨率增长、候选总量增长、每条旧幸存纤维有合法提升。只有第三个条件，配合有效层与有效投影，才支撑逐节点的贪心延伸。

#### 2.2.7 忠实有限编码不改变线程的可计算性

固定有限 $k\ge2$。令 $E_k$ 为自然数到有限字的规范单射编码，有限字的相等可判定，要求编码和在其像上的解码都有效；普通有限 $k$ 进位表示满足这一条件。更一般的有限递归表达式编码也适用，只要确实提供这些终止的双向算法。层编号 $n$ 保留为坐标位置，代码表示 $0\le h<3^n$ 的标准整数代表。

对每个有限层定义

$$
\widetilde H_n=E_k(H_n),
\qquad
\widetilde\pi_n
= E_k\circ\pi_n\circ E_k^{-1}.
\tag{TM.498}
$$

**命题 2.10。** 逐层编码给出相容线程的双射，并且一个编码线程可计算，当且仅当对应的原线程可计算。

**证明。** 因为 $E_k$ 在所用有限表示上可逆，对每个 $n$ 都有双射 $H_n\to\widetilde H_n$。式(TM.498)使相容性等价：

$$
\widetilde\pi_n(E_k(h_{n+1}))=E_k(h_n)
\quad\Longleftrightarrow\quad
\pi_n(h_{n+1})=h_n.
\tag{TM.499}
$$

对可计算原线程，计算第 $n$ 个坐标后运行有限编码算法；对可计算编码线程，计算第 $n$ 个代码后运行解码算法。两方向对每个输入均终止，故保持可计算性。证毕。

因此 $\widetilde H_n$ 仍有统一可判定的有限层、同样的层大小，以及非空但没有可计算点的线程空间。这一结论依赖忠实运输投影，不要求保持时间或空间复杂度。

式(TM.498)并非“取一个无限 $k$ 进代码，再截取其低位”。任意这样的截断未必等于先解码、模 $3^n$ 约化、再编码。若编码改变了投影操作，它描述的就是另一个逆系统，不能直接继承本构造的线程结论。特别地，有限层的可计算双向编码不自动给出任意另一套无限截断语义的相容性。

#### 2.2.8 结论范围与来源

本构造同时实现以下性质：

- 禁用模数大于 $1$、为奇数、互不相同，且均为同一个素数的幂。
- 禁用类有效枚举；每个有界模拟层可完整计算，且候选数量每步严格增长。
- 最终三进幸存集有效闭、Haar 测度至少为 $1/2$，但没有可计算点，也没有普通整数点。
- 每条无限相容候选线程都由最终幸存点实现；单个有限候选不保证可无限延伸。
- 精确可延伸核心具有满射投影，却无法统一有效枚举。
- 在逐事件的实际 LCM 呈现中，有无限多个非满射步骤，且每个都位于实际 LCM 平台。

表达上的不可有效选择来自通用部分计算枚举、对角排除和约束的延迟发现。这里没有证明同余运算本身模拟通用动力系统，也没有给出有限奇数互异模数覆盖、一般存在判定或某个形式理论内独立性的归约。正测度存在、有限成员判定、可计算线程选取以及输入实例的存在性判定，是不同保证。

固定任意奇素数 $p$，将全部 $3$ 替换为 $p$，同一证明给出

$$
\mu_p(K_p)\ge1-\frac1{p-1}
=\frac{p-2}{p-1}>0,
\qquad
|H_n^{(p)}|
\ge p^n-\frac{p^n-1}{p-1}
=\frac{(p-2)p^n+1}{p-1}.
\tag{TM.500}
$$

对 $p\ge3$，下一层这个下界大于本层环境大小 $p^n$，故候选总数同样逐步严格增加。将 $p=2$ 代入式(TM.500)的粗界只给零测度下界；这个粗界本身不判定二进版本的实际测度。

本节三幂对角排除的核心已有仓内公开结果：[profile343 第 10 节](https://github.com/the-omega-institute/trureturing/blob/82c3fcbcce00e4e504dc68583c356d9ec41bd942/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md)给出同一有效柱集构造、至少 $1/2$ 的 Haar 测度下界、无可计算点以及有界模拟的有限候选塔。该结果固定定位于仓库快照 `82c3fcbcce00e4e504dc68583c356d9ec41bd942`。profile343 第 11 节另讨论有限消亡索引问题的条件分类，不将其与这里的无限幸存构造混为一个结论。本节按候选层、精确投影和事件顺序的实际 LCM 呈现保留完整证明及适用边界，不主张这些核心结果的原创性。

不可计算分支的经典背景是 Kleene 树。可核对的直接来源为 Andrej Bauer，[*König’s Lemma and Kleene Tree*](https://math.andrej.com/wp-content/uploads/2006/05/kleene-tree.pdf)，2006 年 5 月 3 日，第 3.3 节、定理 3.5，第 7 页。该定理给出一棵无限递归二叉树却没有可计算无限路径；其证明采用部分可计算函数的对角化与有界时间近似。这里采用相同的经典结构，并用互异素数幂柱集及可求和的测度预算组织排除；正测度下界、实际 LCM 平台结论和有限编码推论的证明均在上文给出，不把这些具体陈述逐字归于该文，也不主张原创性。

有效满射提升及一般同余纤维计数的统一表述见C卷第2.1.1节、C卷第2.1.3节。其满射前提在本例中由无限多次平台删除所破坏；上文C卷第2.2.4节、C卷第2.2.5节已给出此处所需的完整短证。

### 2.3 可计算质量的局部化与点选择

#### 2.3.1 可直接引用的原文

Laurent Bienvenu and Christopher P. Porter, *Deep $\Pi^0_1$ Classes*, **The Bulletin of Symbolic Logic** 22(2), 249–286 (2016), DOI [10.1017/bsl.2016.9](https://doi.org/10.1017/bsl.2016.9)。作者的[研究目录，J20](https://www.labri.fr/perso/lbienvenu/research.html)同时给出这一出版信息及 arXiv 链接。

这里引用的完整证明版本是 [arXiv:1403.0450v3](https://arxiv.org/abs/1403.0450v3)，版本日期 **2017-01-30**；[固定版本 PDF](https://arxiv.org/pdf/1403.0450v3) 共 38 页，**Lemma 3.5 与完整证明均在 PDF 第 11 页，页面印号亦为 11**。这不是已经核验的期刊排版页码，不将它换算为期刊页码。可计算测度的定义在同版本第 5 页。


作者在引理前明确写道：

> “We first need the following lemma, which is folklore.”

Lemma 3.5 的原陈述是：

> “Let $C$ be a $\Pi^0_1$ class. If for some computable probability measure $\mu$ the value of $\mu(C)$ is a positive computable real number, then $C$ contains a computable member.”

这里的空间是二进制 Cantor 空间 $2^{\mathbb N}$；$\Pi^0_1$ 类表示有效闭集。论文的“可计算测度”指所有基本柱集质量 $\mu([\sigma])$ 都能由 $(\sigma,t)$ 一致地近似到误差 $2^{-t}$。它不要求无原子、独立数字或均匀乘积测度。

因此，应归属为**Bienvenu–Porter 文中明确标作 folklore 的引理**，不声称由该论文首创，也不把仓内再次推导视为新定理。

#### 2.3.2 原文证明包含什么

令

$$
\nu(\sigma)=\mu(C\cap[\sigma]).
\tag{TM.632}
$$

原证明先由有效闭性得到 $\nu(\sigma)$ 对 $\sigma$ 一致地右可枚举。对与 $\sigma$ 等长的全部二进制字，有

$$
\nu(\sigma)=\nu(\varnothing)
-\sum_{\substack{|\tau|=|\sigma|\\\tau\ne\sigma}}\nu(\tau).
\tag{TM.633}
$$

由于 $\nu(\varnothing)=\mu(C)$ 可计算，这同时给出一致的左可枚举近似，故全部柱集交质量 $\nu(\sigma)$ 一致可计算。

随后，作者归纳构造长度 $i$ 的相容字 $\sigma_i$，满足

$$
\nu(\sigma_i)\ge\nu(\varnothing)4^{-i}>0.
\tag{TM.634}
$$

每个相应柱集都与 $C$ 相交。它们确定的可计算无限串属于闭集 $C$。

需要保留两个不同范围：

- **局部质量计算**只使用有效闭性、可计算测度及总质量的可计算性，允许总质量为零。
- **选择一个点**还使用严格正的总质量，以保证每层存在可继续选择的正质量子柱。

该证明没有声称可以判定所有柱集是否与 $C$ 相交。非空交集可能质量为零；即便排除这种情况，对一般一致可计算实数的零测试也不是自动可判定的操作。

#### 2.3.3 给定质量名的统一算法与有限字母推广

论文直接陈述的是二进制存在性定理。以下是从它的证明提取的统一算法，并把同一有限分支论证写成有限字母版本；不将这一措辞声称为原文逐字陈述。

设 $\Sigma$ 是给定的有限非空字母表，$k=|\Sigma|$ 已知。输入包括：

1. $C\subseteq\Sigma^{\mathbb N}$ 的有效闭呈示，即补集基本柱的可枚举列表；
2. 测度名，能够一致计算全部 $\mu([\sigma])$；
3. 总质量 $M=\mu(C)$ 的有理 Cauchy 名 $v$，满足 $|v(t)-M|\le2^{-t}$；
4. 用于点选择的有效输入承诺 $M>0$。

前三项足以一致计算全部 $\nu(\sigma)=\mu(C\cap[\sigma])$。具体地，对每个固定长度 $n$，有效闭性及测度名给出一致的有理上界

$$
U_{\tau,s}\downarrow\nu(\tau),\qquad \tau\in\Sigma^n.
\tag{TM.635}
$$

这可由补集枚举的有限阶段及基本柱测度的精度近似取得，不要求这些阶段质量恰为有理数。定义

$$
L_{\sigma,s}
=\max\left\{0,\ v(s)-2^{-s}
-\sum_{\substack{\tau\in\Sigma^n\\\tau\ne\sigma}}U_{\tau,s}\right\}.
\tag{TM.636}
$$

则

$$
L_{\sigma,s}\le\nu(\sigma)\le U_{\sigma,s},
\qquad
U_{\sigma,s}-L_{\sigma,s}\longrightarrow0.
\tag{TM.637}
$$

寻找区间宽度小于所需正有理精度的阶段，就得到 $\nu(\sigma)$ 的统一 Cauchy 名。该构造依赖每层的有限可列举分割；不能直接删除“有限字母”后对任意无限分支树沿用。

对于点选择，$k=1$ 时空间只有一个已知点。若 $k\ge2$，从质量名中搜索并取得有理数 $0<r<M$；例如找到 $v(t)-2^{-t}>0$ 后取其一半。保持不变量

$$
\nu(\sigma_n)\ge r(2k)^{-n}.
\tag{TM.638}
$$

父柱分解为 $k$ 个子柱，故至少一个子柱的质量不小于

$$
\frac{\nu(\sigma_n)}{k}
\ge 2r(2k)^{-(n+1)}.
\tag{TM.639}
$$

并行近似全部子柱质量，选择首个已认证满足

$$
\nu(\sigma_n a)>r(2k)^{-(n+1)}
\tag{TM.640}
$$

的字母 $a$。严格不等式可由有理近似半判定，而上述双倍裕度保证该搜索终止。如此得到一个可计算点；若输入名使用某个 oracle，同一算法输出相对于这些输入名可计算的点。

因此，**给定有效闭呈示、测度名和正总质量名，有统一的点选择算子**。仅知道“存在一个可计算总质量”，而没有其程序或名字，不能当作已经向算法提供了这一输入。该结论也不提供统一的多项式时间界或仅由前缀长度决定的枚举等待阶段界。

标准 $p$ 进数字空间及可计算 Haar 测度满足上述有限字母条件，故可直接按该适配使用。普通几何同胚若未附带有效编码及测度运输，不能自动使用此算法。

### 2.4 正测度幸存集与有限观测认证的边界

奇素数幂对角构造给出一个三进整数集 $K$：它的 Haar 测度至少为 $1/2$，却没有可计算点。这里考察同一个集合在动态规划、随机抽样与有限数字观察接口下能够提供什么。正测度保证随机无限数字流命中 $K$ 的概率；它不保证从一个点的有限数字认证该点属于 $K$。本例中，任何对所有三进整数都可靠的确定性有限数字认证过程，都不能对任何 $K$ 中的点给出正认证。

这是有限正见证与内部非空之间的一般关系在既有对角构造上的应用。结论只针对下文规定的观察接口，不禁止用有限数学证明建立 $K$ 非空，也不禁止借助额外语义前提讨论一个被非计算地定义的点。

#### 2.4.1 固定对象、概率律和输入接口

沿用C卷第2.2.1节唯一固定的程序枚举、事件顺序和C卷第2.2.2节的 Haar 律；本节的全部对象均是同一个对角集合的记号重述：

$$
D=\{e:\varphi_e(e+1)\downarrow\},
\qquad
C_e=\{x\in\mathbb Z_3:x\equiv a_e\pmod{3^{e+1}}\},
\qquad
U=\bigcup_{e\in D}C_e,
\qquad
K=\mathbb Z_3\setminus U.
\tag{TM.501}
$$

每个编号只发出一个柱集，输出按相应模数约化。固定 $\mathbb Z_3$ 的 Haar 概率律 $\mu$。既有对角构造给出

$$
\mu(K)\ge\frac12,
\qquad
K\cap\mathbb Z=\varnothing,
\qquad
K\text{ 不含可计算三进整数}.
\tag{TM.502}
$$

式（TM.502）直接使用C卷第2.2.2节的测度估计与对角证明；程序枚举、最终事件和概率律均未更换。

令 $q_n(x)\in\{0,\ldots,3^n-1\}$ 表示模 $3^n$ 的标准剩余类，并记

$$
[h]_n=\{x\in\mathbb Z_3:q_n(x)=h\},
\qquad
0\le h<3^n.
\tag{TM.503}
$$

$[h]_n$ 是非空的既开又闭柱集，测度为 $3^{-n}$。输入一个三进点，指提供它的数字 oracle：对每个指定位置 $j\ge0$，返回数字 $d_j(x)\in\{0,1,2\}$。每个 oracle 查询都返回正确数字；这些数字不被假定为可计算。读取剩余类 $q_n(x)$ 等价于读取有限多个低位数字。

“动态规划”在本文指对这些有效有限层进行成员检查、计数或有限深度可达性计算；它不隐含无限可延伸性 oracle。“随机抽样”则使用同一个 Haar 律，不能在不同估计中更换实际点或概率分布。

#### 2.4.2 稠密开补集与处处边界

**命题 2.11。** $U$ 是稠密开集；$K$ 是闭的无处稠密集，且

$$
\operatorname{int}(K)=\varnothing,
\qquad
\partial K=K.
\tag{TM.504}
$$

因此没有非空前缀柱集包含在 $K$ 内，每个 $K$ 中的点都是边界点，尽管 $\mu(K)\ge1/2$。

**证明。** 每个 $C_e$ 都开，所以 $U$ 开。任意非空基本柱集 $[h]_n$ 包含普通整数 $h$，而 $\mathbb Z\subseteq U$，故每个这样的柱集都与 $U$ 相交。柱集构成拓扑基，因此 $U$ 稠密。其补集 $K$ 闭且内部为空；闭集内部为空等价于无处稠密。又 $\partial K=\overline K\setminus\operatorname{int}(K)=K$。证毕。

这个论证还给出具体的不可区分成对实例。对任意 $x\in K$ 与任意 $n$，取普通整数 $z=q_n(x)$，则

$$
q_n(z)=q_n(x),
\qquad
x\in K,
\qquad
z\in U.
\tag{TM.505}
$$

前 $n$ 位读数相同，最终成员资格相反。任何只后处理该读数的有限计算都保持这种不可区分性；改变内部状态编码不会补回输入已经合并的区别。

#### 2.4.3 确定性有限数字过程不能给出正认证

考虑一个确定性过程 $A$，其关于输入点 $x$ 的全部信息来自数字 oracle。过程可以自适应地选择查询位置、计算任意长的时间，也可以不终止。要求每次输出“属于 $K$”的运行只做有限次查询并在有限时间结束。全域可靠性指

$$
\forall x\in\mathbb Z_3,\qquad
A^x\text{ 输出“属于 }K\text{”}
\Longrightarrow x\in K.
\tag{TM.506}
$$

过程还可以使用独立于 $x$ 的固定数据和既有定理；假设不允许从别的接口得到与 $x$ 有关的额外信息。

**命题 2.12。** 满足式(TM.506)的这样的过程没有任何正认证运行。特别地，它不能在任何 $x\in K$ 上有限终止并正确地给出正认证。

**证明。** 假设 $A^x$ 存在正认证运行。可靠性先给 $x\in K$。这次运行只查询了有限个位置；取 $n$ 大于全部被查询的位置，无查询时可取 $n=0$。令 $z=q_n(x)$ 为普通整数。$x$ 与 $z$ 在全部被查询位置上的数字相同。

按运行步数归纳，确定性保证两个运行有相同的计算状态、下一次查询、oracle 回复和最终输出。虽然查询规则可以自适应，它在这条共同转录上不会分叉。因此 $A^z$ 也正认证。可是 $z\in U$，违反式(TM.506)。证毕。

等价的拓扑表述是：每条正认证转录包含一个使同一运行成立的非空前缀柱集，故全部正认证输入组成开集。若这个开集包含于 $K$，由 $\operatorname{int}(K)=\varnothing$，它只能为空。无需预先规定统一读取深度；每次接受各自有限，就足以得到结论。

这里“有限正认证”特指由待认证点的有限数字推出成员资格。一个有限证明已经可以推出式(TM.502)的非空性；把某个 $K$ 中的元素通过选择原则或其他非计算定义命名，再证明该名称的性质，使用的是额外语义信息，并不是上述数字观察过程。

#### 2.4.4 负成员资格具有有限可发现见证

**命题 2.13。** 借助点的数字 oracle，性质 $x\notin K$ 可半判定：存在一个统一过程，在且仅在 $x\in U$ 时有限终止并报告不属于 $K$。

**证明。** 按有效交错模拟枚举全部已停机事件 $e\in D$。每发现一个事件，查询足以计算 $q_{e+1}(x)$ 的有限数字，并检查

$$
q_{e+1}(x)\equiv a_e\pmod{3^{e+1}}.
\tag{TM.507}
$$

若相等，报告 $x\in C_e\subseteq U$。报告必可靠。若 $x\in U$，按定义至少有一个相应的 $e$；它将在有限阶段被枚举，且此前只有有限次有限检查，所以过程最终发现该见证。若 $x\in K$，没有任何比较成功，过程不作负报告。证毕。

见证由一个实际停机事件和有限余数比较构成。无报告不等于正证书：它既可能表示点在 $K$ 中，也可能表示排除它的计算尚未停机或尚未被发现。C卷命题2.12 表明，这里的缺失不能单靠对同一个点继续作某个有限数量的数字查询来变成可靠正认证。

#### 2.4.5 有限动态规划与无限可延伸核心

令 $t_e$ 为 $\varphi_e(e+1)$ 的停机步数，未停机时为 $\infty$，并定义既有有限模拟层

$$
H_n=
\{h\in\{0,\ldots,3^n-1\}:
\forall e<n,\ t_e\le n\Longrightarrow
h\not\equiv a_e\pmod{3^{e+1}}\}.
\tag{TM.508}
$$

每层可由有界模拟给出完整列表；模 $3^n$ 约化把 $H_{n+1}$ 映入 $H_n$。同时

$$
|H_n|\ge\frac{3^n+1}{2},
\qquad
K=\varprojlim_n H_n.
\tag{TM.509}
$$

对 $m\ge n$，定义深度 $m$ 所见的第 $n$ 层可达核心及其精确极限

$$
B_{n,m}
=\{h<3^n:\exists y\in H_m,\ y\bmod3^n=h\},
\qquad
R_n=q_n(K).
\tag{TM.510}
$$

$B_{n,m}$ 可计算，可用有限枚举或从第 $m$ 层向下回传可达标记的动态规划求出。随着 $m$ 增大，它们满足

$$
B_{n,m+1}\subseteq B_{n,m},
\qquad
R_n=\bigcap_{m\ge n}B_{n,m}.
\tag{TM.511}
$$

**命题 2.14。** 对标准节点 $h<3^n$，

$$
h\notin R_n
\quad\Longleftrightarrow\quad
\exists m\ge n:
\{y\in H_m:y\bmod3^n=h\}=\varnothing.
\tag{TM.512}
$$

因此 $R_n$ 的补集可关于 $(n,h)$ 统一有效枚举，即精确核心族统一 co-c.e.。

**证明。** 若某个有限深度已无后继，任何无限线程都不可能经过 $h$，故 $h\notin R_n$。反过来，若每个深度 $m\ge n$ 都有一个以 $h$ 开头的合法节点，取这些节点及其前缀形成树。有限层相容性使它前缀封闭，每个节点最多有三个孩子，而且树有任意深的节点。有限分支树的 König 引理给出一条经过 $h$ 的无限分支。由式(TM.509)，它对应某个 $x\in K$，因此 $h\in R_n$。取逆否命题得另一方向。式(TM.512)右侧每个给定 $m$ 的空集检查都可计算，逐个搜索 $m$ 即可枚举补集。证毕。

这里的有限见证是“整个后继子树在某一有限深度已经消失”，与点本身的单个禁用柱集见证相容。König 引理给数学存在，不提供可计算分支选择。

**命题 2.15。** 核心族 $R_n$ 不能关于 $n$ 统一有效枚举。因而虽然对每个固定 $n$，有限递减链 $B_{n,m}$ 最终稳定为 $R_n$，却不存在一个总可计算函数 $b(n)\ge n$，保证对所有 $n$ 都有 $B_{n,b(n)}=R_n$。

**证明。** C卷第2.2.4节已证明同一个 $K$ 的精确投影族 $R_n=q_n(K)$ 不可统一枚举：其自然连接满射，若有枚举即可从唯一根逐层搜索兼容提升，得到被对角构造排除的可计算线程。本节的 $R_n$ 与那里完全相同，因此直接应用该结论。

对固定 $n$，$B_{n,m}$ 是有限集合内的递减链，故存在某个有限稳定阶段；式(TM.511)说明稳定值为 $R_n$。若所述 $b$ 可计算，计算 $B_{n,b(n)}$ 就给出 $R_n$ 的统一完整列表，与前一结论矛盾。证毕。

每个单独固定的有限 $R_n$ 当然有有限列表；这里否定的是从输入 $n$ 统一有效取得正确列表。有限动态规划可以准确回答给定深度的可达性，也可发现最终不能延伸的节点；它不能从“搜索到当前仍有后继”自动得到无限延伸的正证书。

#### 2.4.6 Haar 抽样的成功事件与有限输出

取独立均匀三进数字 $D_j\in\{0,1,2\}$，以三进极限定义

$$
X=\sum_{j\ge0}D_j3^j.
\tag{TM.513}
$$

其有限剩余类均匀分布，因此 $X$ 服从同一个 Haar 律 $\mu$。式(TM.502)直接给出

$$
\mathbb P(X\in K)=\mu(K)\ge\frac12.
\tag{TM.514}
$$

这是关于完整无限随机数字流的事件概率，不是一份在有限时刻完成的三进点输出，也不是一个能在命中时停下并确认命中的算法。

可计算三进点的集合可数，而每个单点的 Haar 测度至多 $3^{-n}$ 对所有 $n$ 成立，故单点测度为零。因此 Haar 随机点以概率 $1$ 不可计算。这与有限程序可以逐个请求随机数字并不矛盾：程序依赖外部无限随机流，尚未读出的随机位不属于已经完成的有限结果。

若一个有限终止的随机过程只输出有限代码，并保证该代码是一份不再调用外部随机源或非计算 oracle 的总剩余类算法，那么每个这样的输出点都是可计算点，因此没有一个属于 $K$。若过程返回的是仍将读取未来随机数字的惰性对象或 oracle 句柄，它返回了一个流接口；这可以表示式(TM.513)的随机点，但不能被改称为已完成的有限点计算或成员认证。

还有一个更局部的概率边界。

**命题 2.16。** 对每个非空前缀柱集，

$$
\mathbb P(X\in K\mid q_n(X)=h)
=\frac{\mu(K\cap[h]_n)}{\mu([h]_n)}
<1.
\tag{TM.515}
$$

**证明。** $U$ 稠密开，所以 $U\cap[h]_n$ 非空且开，包含某个更细的非空柱集。该细柱集有正 Haar 测度，故 $\mu(U\cap[h]_n)>0$，从而 $\mu(K\cap[h]_n)<\mu([h]_n)$。证毕。

式(TM.515)不主张这些条件概率有统一的离 $1$ 距离，也不主张它们都严格大于零。一个有限候选前缀甚至可以没有任何最终幸存后继。它表明：全局命中概率至少 $1/2$ 不等于每条有限读数都可靠，更不等于某条有限读数能提供概率为 $1$ 的成员保证。

#### 2.4.7 Monte Carlo 在有限层估计的究竟是什么

把有限候选层提升回同一个概率空间：

$$
A_n=q_n^{-1}(H_n),
\qquad
A_{n+1}\subseteq A_n,
\qquad
\bigcap_nA_n=K.
\tag{TM.516}
$$

每个 $A_n$ 的成员资格可用有限随机数字和有限模拟准确判定，其概率为可计算有理数

$$
p_n=\mathbb P(X\in A_n)=\frac{|H_n|}{3^n},
\qquad
p_n\downarrow\mu(K)\ge\frac12.
\tag{TM.517}
$$

最后的极限等式来自概率测度对递减可测集的从上连续性。对固定 $n$，独立重复抽取前 $n$ 位并检查 $H_n$，得到的是事件 $A_n$ 的 Bernoulli 样本。由此可以估计有限阶段的存活概率 $p_n$；直接枚举也可精确计算它。这里未作计算复杂度优势断言。

若把一次通过 $H_n$ 的有限测试叫作“已命中 $K$”，就替换了被估计的事件。真正的 $K$ 还要求通过所有后续阶段；单个样本在当前阶段未被排除，不是完成的正认证。式(TM.517)本身也没有提供由误差要求求出充分阶段号的算法。

对同一条无限随机流，可以并行运行C卷第2.4.4节的负半判定过程：落在 $U$ 的样本最终被拒绝，落在 $K$ 的样本永远不会因禁用柱集被拒绝。没有一个有限“尚未拒绝”时刻自动升级为确定命中。正测度、概率估计、无限流的持续生成，以及可靠的有限停止证书，分别对应不同的输出承诺。

#### 2.4.8 总质量不可计算，有限层概率没有可计算收敛模量

下述一般命题只用有效闭集的柱集呈现、有限可加性和紧致性；这里将其应用于固定的 $K$，不作原创性主张。

**命题 2.17。** 若 $F\subseteq\mathbb Z_3$ 有效闭，$\mu(F)>0$，且实数 $\mu(F)$ 可计算，则 $F$ 含可计算点。更精确地，给定 $F$ 的有效闭呈现和 $\mu(F)$ 的可计算实数名称，可在正测度承诺下统一计算这样一个点；不必另给正测度的数值下界。

**证明。** 在C卷第2.3.3节的有限字母统一算法中取 $\Sigma=\{0,1,2\}$、$C=F$、测度为可计算 Haar 律，并给入本命题的质量名。有效闭呈示是同一补集柱枚举，$M>0$ 是点选择承诺；故该算法直接给出所需可计算点。此处无需预先给出正下界，算法从质量名搜索得到它。

为明确这一实例的计算输入，有限阶段补集给出

$$
F_{s+1}\subseteq F_s,\qquad \bigcap_sF_s=F,\qquad f_s:=\mu(F_s)\downarrow M.
\tag{TM.518}
$$

阶段 $s$ 按计算时间截断，没有新事件也结束；柱并的共同有限细化允许精确有理计数。对深度 $n$ 和标准节点 $h<3^n$，记

$$
m_{n,h}=\mu(F\cap[h]_n),\qquad u_{n,h,s}=\mu(F_s\cap[h]_n).
\tag{TM.519}
$$

若质量名满足 $|v_t-M|\le2^{-t}$，令 $\ell_t=v_t-2^{-t}$。一般算法在这个等质量分割上的区间就是

$$
L_{n,h,s,t}=\max\left\{0,\ell_t-\sum_{\substack{0\le r<3^n\\r\ne h}}u_{n,r,s}\right\},
\qquad L_{n,h,s,t}\le m_{n,h}\le u_{n,h,s},
\tag{TM.520}
$$

以及

$$
0\le u_{n,h,s}-L_{n,h,s,t}\le f_s-\ell_t\longrightarrow0.
\tag{TM.521}
$$

因此搜索 $f_s-\ell_t<2^{-k}$ 给所需精度，有限和有 $3^n-1$ 项；并未给多项式时间界。取 $\ell_t>0$ 后逐层选择首个被严格正下界认证的孩子，正是C卷第2.3.3节的选择过程，不要求决定其余孩子是否零质量，也不声称得到数值最小的正质量孩子。嵌套非空紧集及相容前缀的唯一点论证同该节。证毕。

**推论 2.18。** 对本文固定的对角幸存集，

$$
\mu(K)\text{ 不可计算}.
\tag{TM.522}
$$

否则式(TM.502)的正测度与C卷命题2.17 会给出 $K$ 中的可计算点，违背同一式中的对角结论。已知的 $\mu(K)\ge1/2$ 只是一个正下界，不提供任意精度的总质量下逼近；它不能替代C卷命题2.17 假设中的可计算实数名称。

因此，式(TM.517)的这条固定可计算有理数列 $p_n\downarrow\mu(K)$ 没有总可计算的收敛模量。具体地，不存在总可计算 $b:\mathbb N\to\mathbb N$ 使

$$
\forall k\ \forall n\ge b(k),\qquad
0\le p_n-\mu(K)\le2^{-k}.
\tag{TM.523}
$$

若存在，计算有理数 $p_{b(k)}$ 就以误差至多 $2^{-k}$ 计算出 $\mu(K)$，与式(TM.522)矛盾。这并不否定有限层概率的准确计算，也不否定它们作为上逼近的收敛；被排除的是从任意精度要求有效取得保证达到该精度的阶段号。

#### 2.4.9 哪些前提改变后不再适用

有限正认证不可能性需要全域可靠性和有限数字接口。以下情形改变了问题，不能用C卷命题2.12 一概排除：

- 输入附有额外的全局承诺 $x\in P$ 时，可靠性可以只要求在 $P$ 上成立；可能存在柱集 $V$ 使 $\varnothing\ne V\cap P\subseteq K$。极端情况下，承诺 $P=K$ 已经给出成员资格。
- 输入提供完整语义描述、与该点相关的外部 oracle、证明对象或其他额外信息时，信息不再只来自有限数字。须另行核对这些信息的正确性和取得条件。
- 只认证 $x\in A_n$、有限深度仍有后继，或某个明确有限同余族未覆盖时，目标本身是有限事件，可以通过相应有限层判定。
- 允许一定误判概率时，可以讨论统计决策；这改变了式(TM.506)的可靠性要求，不能将置信度改称为无误成员证书。
- 若换成具有非空内部的目标集，包含于目标的非空柱集本身就是有限正见证。若目标既开又闭且已给出有效有限商描述，则可直接有限判定。

因此，本例不否定动态规划、Monte Carlo 或有限观察的各自用途。它确定的是在这个实际对象和指定接口上，哪些输出可以可靠给出，哪些需要额外信息或更弱的保证。

#### 2.4.10 既有结果与来源边界

对角集合、有效有限层以及无可计算线程的构造，见C卷第2.2节。本文固定其同一个 $K$ 和同一个 Haar 律；没有改变禁用同余族来适配不同结论。该构造的经典可计算性背景是 Andrej Bauer，[*König’s Lemma and Kleene Tree*](https://math.andrej.com/wp-content/uploads/2006/05/kleene-tree.pdf)，2006 年 5 月 3 日，定理 3.5；本文不主张构造或一般有限观察判据的原创性。

仓内对应普通数学成果为不可变快照 82c3fcbcce00e4e504dc68583c356d9ec41bd942 中的 [profile 343](https://github.com/the-omega-institute/trureturing/blob/82c3fcbcce00e4e504dc68583c356d9ec41bd942/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md)：

- profile343 第 8 节给出有限正见证的精确条件 $\varnothing\ne q_n^{-1}(h)\subseteq F$，并将其等同于前缀拓扑中内部非空；C卷第2.4.2节、C卷第2.4.3节是在 $F=K$ 上的应用，包含自适应查询的具体运行证明。
- profile343 第 10 节已经给出相同三幂对角构造、正测度、无可计算点、可判定有限层、严格候选数量增长，以及有效满射提升与延迟低层约束的区别。本文将这些既有性质连接到正负认证和随机流接口。
- profile343 第 9 节给出另一个无限奇素数例子，其相容完成分支不由整数实现，而极限测度为零；它不等同于这里正测度且没有可计算分支的例子。
- profile343 第 11 节对指定奇数互异流的有限消亡指标问题作条件分类；本文没有新增从该问题到本例的归约，也没有把有限认证障碍变成有限覆盖问题或形式独立性的结论。

有限分支树的紧致性、开集的有限观察性质及 Haar 测度的连续性是上述连接所用的通常数学事实。结果的适用范围由数字 oracle、全域可靠性、共同概率律和无限呈现四项前提明确限定。

### 2.5 对角集合的严格质量界与后验上确界

#### 2.5.1 对角三进幸存集的严格质量界

以下两项是针对固定对角构造的短推论，和上面的 folklore 引理分开归属。

沿用C卷第2.2.1节的同一有效编号、最终集合 $K$ 与 Haar 律。按深度标记该节的禁柱，即将原 $C_e$ 在这里写成 $C_{e+1}$：

$$
C_{e+1}=[a_e\bmod3^{e+1}]_{e+1}\subseteq\mathbb Z_3.
\tag{TM.641}
$$

令 $K$ 为剩余闭集，$\mu$ 为归一化 Haar 概率。每个正深度至多禁去一个柱，且对角论证排除所有可计算三进点。

这一集合实际满足严格界

$$
\frac12<\mu(K)<1.
\tag{TM.642}
$$

证明：编号表中存在处处不停止函数的某个索引 $e_\infty$，该深度永远没有事件。因此

$$
\mu(\mathbb Z_3\setminus K)
\le\sum_{e\ne e_\infty}3^{-(e+1)}
=\frac12-3^{-(e_\infty+1)},
\tag{TM.643}
$$

从而

$$
\mu(K)\ge\frac12+3^{-(e_\infty+1)}>\frac12.
\tag{TM.644}
$$

另一方面，编号表中也有常零全函数的某个索引 $e_0$；其事件禁去一个质量 $3^{-(e_0+1)}$ 的柱，故

$$
\mu(K)\le1-3^{-(e_0+1)}<1.
\tag{TM.645}
$$

这些显式间隔依赖所固定的函数编号，不将未给出的索引替换成统一数值常数。禁柱之间即使重叠，上述两个不等式也成立。

#### 2.5.2 每个有限柱的后验都小于一，整体上确界却是一

对每个非空有限柱 $D=[b]_d$，有

$$
\frac{\mu(K\cap D)}{\mu(D)}<1.
\tag{TM.646}
$$

证明：整数代表 $b$ 是 $D$ 中的一个可计算三进点，故被某个禁柱 $C_h$ 排除。两个柱相交必嵌套。若 $h\le d$，则 $D\subseteq C_h$，该比值为零；若 $h>d$，则 $C_h\subseteq D$，于是

$$
\frac{\mu(K\cap D)}{\mu(D)}
\le1-3^{d-h}<1.
\tag{TM.647}
$$

但没有一个统一正间隔将所有这些比值压在 $1$ 以下。令 $R_n$ 为与最终 $K$ 相交的深度 $n$ 柱的剩余类集，并令

$$
B_n=\bigcup_{b\in R_n}[b]_n,
\qquad a_n=\mu(B_n),\qquad M=\mu(K)>0.
\tag{TM.648}
$$

每个点若属于 $B_n\setminus K$，只能被深度大于 $n$ 的禁柱排除，否则整个所在深度 $n$ 柱将不再可延伸。因此

$$
0\le a_n-M\le\sum_{h>n}3^{-h}=\frac{3^{-n}}2.
\tag{TM.649}
$$

$R_n$ 非空，而且其柱质量相同，故对这些柱的条件概率取平均得到

$$
\max_{b\in R_n}
\frac{\mu(K\cap[b]_n)}{\mu([b]_n)}
\ge\frac{M}{a_n}
\ge\frac{M}{M+3^{-n}/2}
\longrightarrow1.
\tag{TM.650}
$$

结合所有条件概率都至多为 $1$，有

$$
\sup_{d\ge0,\,0\le b<3^d}
\frac{\mu(K\cap[b]_d)}{\mu([b]_d)}=1,
\tag{TM.651}
$$

而这个上确界不在任何有限柱达到。证明中的 $R_n$ 是最终延拓核；该极值存在论证没有把它冒充为可由有限枚举阶段直接取得的列表，也没有给出选择近极值柱的有效时间保证。

这些是普通数学核对结果，不是新增 Lean 核验、形式独立性结果或原创性鉴定。

### 2.6 不同深度柱集的规范表示、有效性与局部分裂

本节固定实际的前缀塔，研究“每个深度至多使用一个柱集”究竟约束了什么。以下给出普通数学推导、有效性反例及运输条件；不宣称已经完成 Lean 核验、文献穷尽或原创性鉴定。其用途是补齐完成化表示与实际离散接口之间的条件，不能由此结算有限互异奇模数覆盖问题。

可复用的协作基础是 [profile343 的第 13 节，固定提交 c2258c72a04890a997f2c5796a64be5a7247c0f9](https://github.com/the-omega-institute/trureturing/blob/c2258c72a04890a997f2c5796a64be5a7247c0f9/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md#13-exact-cylinder-extendibility-with-one-forbidden-class-per-prime-power-height)：它已经给出奇素数、每高度至多一个最终禁类时的柱集可延伸判据、条件正测度界，以及最终高度表与可枚举事件流之间的有效性区别。本节不把这些已有结论重新计为成果；补充的对象是规范最小柱基、二进制边界、可枚举性失配和接口运输。

#### 2.6.1 固定前缀塔与深度零约定

固定素数 $p\ge2$，令

$$
X=\mathbb Z_p\cong\{0,1,\ldots,p-1\}^{\mathbb N}.
\tag{TM.602}
$$

数字按低位到高位读取。有限字 $s=(s_0,\ldots,s_{d-1})$ 的柱集为

$$
[s]=\{x\in X:x_i=s_i\ (0\le i<d)\}
=\left(\sum_{i<d}s_ip^i\right)+p^d\mathbb Z_p.
\tag{TM.603}
$$

其深度是 $|s|=d$，归一化 Haar 质量为 $p^{-d}$。深度零的唯一柱集是空字对应的根 $[\varnothing]=X$。两个柱集相交当且仅当一个包含另一个。

对开集 $U\subseteq X$，定义规范最小前缀基

$$
\operatorname{Min}(U)=
\begin{cases}
\{X\},&U=X,\\
\{[s]: |s|\ge1,\ [s]\subseteq U,\ [s^-]\not\subseteq U\},&U\ne X,
\end{cases}
\tag{TM.604}
$$

其中 $s^-$ 删掉最后一个数字。这里“最小”指已能认证属于 $U$ 的最短前缀；按集合包含关系，它们是 $U$ 内的极大柱集。特别地，$\operatorname{Min}(\varnothing)=\varnothing$。

每个 $x\in U$ 都有一个包含于 $U$ 的柱邻域。在沿 $x$ 的前缀链上，取具有这一性质的最小深度，就得到 $\operatorname{Min}(U)$ 的一个成员。因此

$$
U=\bigcup_{C\in\operatorname{Min}(U)}C.
\tag{TM.605}
$$

这些最小柱集两两不交：若两个相交而不相等，则一个严格包含另一个，后者的父柱也包含于 $U$，与最小性矛盾。

#### 2.6.2 不同深度表示的精确拓扑判据

允许深度零时，对任意开集 $U\subseteq\mathbb Z_p$，以下两项等价：

1. $U$ 是一族深度两两不同的柱集的并。
2. $\operatorname{Min}(U)$ 在每个深度至多含一个柱集。

而且，只要第一项成立，**每个规范最小柱集都必须实际出现在每一份这样的表示中**。

证明必要性。设

$$
U=\bigcup_{i\in I}D_i,
\qquad \operatorname{depth}(D_i)\ne\operatorname{depth}(D_j)\quad(i\ne j),
\tag{TM.606}
$$

并取 $C\in\operatorname{Min}(U)$。任何与 $C$ 相交的 $D_i$ 都与之嵌套。若 $D_i$ 严格包含 $C$，则 $C$ 的父柱也包含于 $U$，与最小性矛盾；根柱没有严格祖先。因此所有与 $C$ 相交的生成柱都包含于 $C$。

假设其中没有 $C$ 自身。它们就都是 $C$ 的真后代，却仍覆盖 $C$。柱集 $C$ 紧致，故存在有限子覆盖 $D_{i_1},\ldots,D_{i_k}$。它们相对于 $C$ 的深度

$$
r_j=\operatorname{depth}(D_{i_j})-\operatorname{depth}(C)
\tag{TM.607}
$$

是两两不同的正整数。令 $R=\max_j r_j$，用 $C$ 上归一化的限制 Haar 测度计算，有

$$
1
\le\sum_{j=1}^k p^{-r_j}
\le\sum_{r=1}^{R}p^{-r}
=\frac{1-p^{-R}}{p-1}
<1.
\tag{TM.608}
$$

矛盾。因此 $C$ 必须在生成族中出现，而每深度至多一个的限制也传递到 $\operatorname{Min}(U)$。

充分性由C卷第2.6.1节的规范基覆盖公式直接得到。

上述证明同时适用于 $p=2$。这一端点不能用无穷质量和的严格不等式代替紧致性：$\sum_{r\ge1}2^{-r}=1$，但每个有限子和仍严格小于 $1$。例如低位在前的二进制柱

$$
[0],\ [10],\ [110],\ldots
\tag{TM.609}
$$

两两不交、每深度恰好一个，其并是

$$
\mathbb Z_2\setminus\{-1\},
\tag{TM.610}
$$

因为遗漏的唯一数字串是 $111\ldots$。该并的 Haar 质量是 $1$，仍不等于整个空间。

如果只允许真模数 $p^d>1$，即只允许 $d\ge1$，判据必须写成

$$
U\ne X
\quad\text{且}\quad
\#\{C\in\operatorname{Min}(U):\operatorname{depth}(C)=d\}\le1
\quad\text{对所有 }d\ge1.
\tag{TM.611}
$$

若遗漏 $U\ne X$，根柱会造成错误的充分性结论。空集仍可由空族表示。

最后，任何额外生成柱都包含于唯一一个规范最小柱集，因而是冗余的。故每份不可再删的不同深度表示，恰好就是 $\operatorname{Min}(U)$。这是相对于固定前缀塔的规范性，不是相对于任意坐标变换的规范性。

#### 2.6.3 拓扑规范形不等于可枚举规范形

柱集有有限数字编码。若 $\operatorname{Min}(U)$ 可枚举且每个深度至多一个，就能枚举一份不同深度表示。但其逆命题不成立：**一个可枚举、每深度至多一柱的生成族，可以具有不可枚举的规范最小柱基。**

取任意可枚举但不可判定的集合 $A\subseteq\mathbb N$。对每个 $e\ge0$ 定义

$$
B_e=[1^{2e}0],\qquad D_e=[1^{2e}00].
\tag{TM.612}
$$

其中 $1^{2e}$ 表示连续 $2e$ 个数字 $1$。于是

$$
\operatorname{depth}(B_e)=2e+1,
\qquad
\operatorname{depth}(D_e)=2e+2,
\qquad D_e\subsetneq B_e.
\tag{TM.613}
$$

各 $B_e$ 两两不交：若 $e<f$，$B_e$ 在位置 $2e$ 的数字是 $0$，而 $B_f$ 在该位置是 $1$。令

$$
U=\bigcup_{e\ge0}D_e\ \cup\ \bigcup_{e\in A}B_e.
\tag{TM.614}
$$

枚举全部 $D_e$，并在 $e$ 进入 $A$ 时枚举 $B_e$，得到 $U$ 的可枚举生成族；偶深度只使用 $D_e$，奇深度只使用对应的 $B_e$，故每深度至多一柱。

若 $e\notin A$，则 $U\cap B_e=D_e$，所以 $D_e$ 是规范最小柱集。若 $e\in A$，则 $B_e\subseteq U$，其父柱 $[1^{2e}]$ 却不包含于 $U$：全 $1$ 数字串属于该父柱，并且不属于任何 $B_f$。这一论证也包含 $e=0$ 的根父柱。因而 $B_e$ 是规范最小柱集，$D_e$ 则冗余。由两两不交性以及C卷第2.6.1节的覆盖结论，得到精确等式

$$
\operatorname{Min}(U)
= \{D_e:e\notin A\}\ \cup\ \{B_e:e\in A\}.
\tag{TM.615}
$$

如果这个最小柱基可枚举，就可在其枚举中等待 $D_e$ 的有限代码出现，由此枚举 $\mathbb N\setminus A$。但 $A$ 及其补集同时可枚举会使 $A$ 可判定，矛盾。

因此，正规形在集合论上唯一且实际包含在每份不同深度表示中，仍不意味着能够从一份有效枚举中有效地删去全部冗余项。困难来自确认“父柱将来不会被补满”所需的否定信息；不断枚举当前最小项并允许撤回，也不是最终最小基的单调枚举。

这个反例适用于所有素数 $p\ge2$，只用到了数字 $0,1$。它没有给出任意有效开集何时存在有效不同深度表示的完整判定程序；这里保留的精确结论是：可枚举最小基是充分条件，却不是必要条件。

profile343 第13节已经区分“最终高度表可判定”和“禁类仅以事件流给出”，并提醒冗余禁类的原始清单不能从幸存集合中自动恢复。上述反例把这种信息区别具体落在规范基的可枚举性上，不改变该节既有结算。

#### 2.6.4 仿射局部分裂及其有限性条件

转到整数的 profinite 完成化 $\widehat{\mathbb Z}$，写

$$
C(a,m)=a+m\widehat{\mathbb Z},\qquad a\in\mathbb Z,\ m\ge1.
\tag{TM.616}
$$

映射

$$
\theta_{a,m}:\widehat{\mathbb Z}\longrightarrow C(a,m),
\qquad t\longmapsto a+mt
\tag{TM.617}
$$

是同胚。乘以 $m$ 的单射性可直接从有限商看出：若 $mt=0$，在模 $mn$ 上读取便得到 $t=0\pmod n$，这对每个 $n$ 成立，故 $t=0$。像是模 $m$ 读数的零核；反过来，若 $x=0\pmod m$，则把 $x\pmod {mn}$ 的可被 $m$ 整除的代表除以 $m$，得到相容的模 $n$ 剩余类，从而得到 $x=mt$。连续双射从紧空间到 Hausdorff 子空间自动为同胚。

对任意指标族 $(b_j,r_j)$，其中 $b_j\in\mathbb Z$、$r_j\ge1$，有逐项等式

$$
\theta_{a,m}\bigl(C(b_j,r_j)\bigr)
=C(a+mb_j,mr_j).
\tag{TM.618}
$$

所以对任意有限或无限族，都有

$$
C(a,m)=\bigcup_j C(a+mb_j,mr_j)
\quad\Longleftrightarrow\quad
\widehat{\mathbb Z}=\bigcup_j C(b_j,r_j).
\tag{TM.619}
$$

**只有在族有限时，才可直接再等价为覆盖全部普通整数：**

$$
C(a,m)=\bigcup_{j=1}^{k} C(a+mb_j,mr_j)
\quad\Longleftrightarrow\quad
\mathbb Z=\bigcup_{j=1}^{k}(b_j+r_j\mathbb Z).
\tag{TM.620}
$$

右向左使用了有限性：有限个柱集的并既开又闭，若包含稠密的 $\mathbb Z$，就包含其闭包 $\widehat{\mathbb Z}$。也可以在模 $\operatorname{lcm}(r_1,\ldots,r_k)$ 的同一个有限商上逐剩余类核对。左向右则只需与整数取交。

无限族不存在这个自动推论。沿用 profile343 第 9 节的整数枚举覆盖构造，枚举全部整数为 $(z_j)_{j\ge0}$，逐项取严格递增的奇素数 $q_j>2^{j+2}$。每个整数属于相应的 $z_j+q_j\mathbb Z$，故这些类覆盖 $\mathbb Z$。但在同一个完成化空间中，归一化 Haar 测度满足

$$
\mu\left(\bigcup_{j\ge0}C(z_j,q_j)\right)
\le\sum_{j\ge0}\frac1{q_j}
<\frac12.
\tag{TM.621}
$$

因此它们没有覆盖 $\widehat{\mathbb Z}$。这不是有限覆盖问题的反例，而是“覆盖稠密子集”不能代替“覆盖整个紧空间”的无限族反例。

局部分裂中还有三项不可省略的算术限制：

- 子柱真包含于父柱，当且仅当相对模数 $r_j>1$；允许 $r_j=1$ 会把父柱本身作为平凡分裂。
- 子模数 $mr_j$ 两两互异，当且仅当 $r_j$ 两两互异。
- 若父模数 $m$ 为奇数，则子模数全部为奇数，当且仅当全部相对模数 $r_j$ 为奇数。

这种仿射参数化涵盖所有真正包含于父柱的同余子柱。事实上

$$
C(c,n)\subseteq C(a,m)
\quad\Longleftrightarrow\quad
m\mid n\ \text{且}\ c\equiv a\pmod m.
\tag{TM.622}
$$

必要性可取子柱中的两个整数 $c,c+n$；充分性直接代入。故所有子柱都可写成 $n=mr$、$c=a+mb$ 的形式。

于是，将一个奇父模数柱集精确替换为**有限个、真包含、模数互异且为奇数**的子柱，恰好要求找到相对模数 $r_j>1$ 的有限互异奇模数整数覆盖。它就是原覆盖问题的一份仿射复制，不是一项可以免费执行的编码正规化。若嵌入一个已有的全局模数族，还必须核对子模数 $mr_j$ 不与外部未替换模数碰撞；局部互异不蕴含全局互异。

对于无限族，若真覆盖了父柱，紧致性仍会选出有限子覆盖；但只覆盖父柱内的普通整数，不足以调用这一步。

#### 2.6.5 同胚和单调换坐标都不自动运输前缀接口

C卷第2.6.2节的判据依赖指定的深度函数和前缀柱族。相同基数、相同测度、可计算同胚，都不足以保留这份约束。

在二进制数字空间中取

$$
V=[0],\qquad U=[00]\cup[10].
\tag{TM.623}
$$

两者的 Haar 质量均为 $1/2$。$V$ 的规范最小基只有一个深度 $1$ 柱集；$U$ 的规范最小基却恰有两个深度 $2$ 柱集，所以 $U$ 没有不同深度柱集表示。交换数字位置 $0$ 与 $1$ 是一个可计算、保 Haar 测度的同胚，且把 $V$ 送到 $U$。它保留完成化空间和概率结构，却没有保留原生的前缀深度接口。

即便要求数字字典序下严格单调，同胚仍不必保留同一深度读数或移位操作。定义

$$
h(0\alpha)=00\alpha,
\qquad
h(10\alpha)=01\alpha,
\qquad
h(11\alpha)=1\alpha.
\tag{TM.624}
$$

这里 $\alpha$ 是任意无限二进制尾串。前缀族 $\{0,10,11\}$ 与 $\{00,01,1\}$ 都是完整无前缀冲突的有限分割，并按相同的字典序排列，所以 $h$ 是具有可计算逆的严格字典序递增同胚。这里使用的是低位在前的数字串字典序，没有给 $\mathbb Z_2$ 宣称一个相容的算术有序域结构。

设 $q_1$ 读首位。以 $10$ 开头和以 $11$ 开头的两个输入有相同的 $q_1$，其像却分别以 $0$ 和 $1$ 开头。因此不存在函数 $g$ 使

$$
q_1h=gq_1.
\tag{TM.625}
$$

设 $S$ 删除首位。对 $x=1000\ldots$，直接计算

$$
h(Sx)=0000\ldots,
\qquad
S(hx)=1000\ldots,
\tag{TM.626}
$$

所以 $hS\ne Sh$。

当然，可以显式运输整套接口：

$$
q'_n=q_nh^{-1},\qquad S'=hSh^{-1}.
\tag{TM.627}
$$

这样才有 $q'_nh=q_n$ 与 $S'h=hS$。此时新的观察一般不再是新坐标下同深度的原生前缀读取；原来的深度、计算预算、代价及模数互异约束是否继续保留，还需各自给出运输规则。

#### 2.6.6 对“离散步骤—完成化极限—体边关系”的具体约束

在这个模型中，完成化点由一整条相容前缀线程刻画，柱集是有限观察留下的候选纤维，开集则由有限正见证组成。这是一种明确的表示关系。

本节进一步显示，保持完成化对象与保持接口是不同的证明义务：

$$
\text{同一个开集}
\quad\not\Rightarrow\quad
\text{可有效取得其规范基};
\tag{TM.628}
$$

$$
\text{同胚且保测度}
\quad\not\Rightarrow\quad
\text{保持原前缀深度与每层一个的约束};
\tag{TM.629}
$$

$$
\text{覆盖全部整数}
\quad\not\Rightarrow\quad
\text{无限族覆盖完成化};
\tag{TM.630}
$$

$$
\text{可逆的局部仿射坐标}
\quad\not\Rightarrow\quad
\text{免费得到有限互异奇模数分裂}.
\tag{TM.631}
$$

因此，把离散与完成化称作同一结构的两种表示时，需要指明共同对象以及被运输的观察和操作。若再把它们解释成“体—边”，仍须额外指定哪个对象是体、哪个接口是边、怎样恢复，以及有限步骤和有效资源保留到什么程度。本节的具体定理与反例提供这些核对条件，不从命名本身推出物理空间、物理时间或一个无条件的全息原理。

### 2.7 Exact mass and cylinder extendibility under sparse prime-power exclusions

#### 2.7.1 Fixed presentation and the positive cylinder gap

**定义 2.19。** Fix an odd prime $p$ and normalized Haar probability $\mu$ on $\mathbb Z_p$. Write
$$
[b]_d=\{x\in\mathbb Z_p:x\equiv b\pmod{p^d}\},
\qquad d\ge0,\quad 0\le b<p^d.
\tag{TM.561}
$$
Thus $[0]_0=\mathbb Z_p$ and $\mu([b]_d)=p^{-d}$. A fixed computably enumerable event presentation includes, at each positive depth $h$, either no forbidden cylinder or one final cylinder
$$
C_h=[a_h]_h.
\tag{TM.562}
$$
Repeated announcements of the same cylinder have no effect. The restriction is on the final set of cylinders at each depth; announcements may arrive in any order, and a small-depth cylinder may appear arbitrarily late. Define
$$
E=\mathbb Z_p\setminus\bigcup_{h:\,C_h\text{ included}}C_h,
\qquad
M=\mu(E),
\qquad
R=\{(d,b):E\cap[b]_d\ne\varnothing\}.
\tag{TM.563}
$$
The set $E$ is effectively closed. All masses and extension queries below concern this same final set, this same presentation, and this same Haar law.

**命题 2.20（sparse ancestor criterion）。** Put
$$
c_p=\frac{p-2}{p-1},
\qquad
\delta_d=c_pp^{-d}>0.
\tag{TM.564}
$$
For $D=[b]_d$, the following are equivalent:

1. $E\cap D\ne\varnothing$.
2. No included $C_h$ with $h\le d$ contains $D$.
3. $\mu(E\cap D)\ge\delta_d$.

In particular, each cylinder mass belongs to
$$
\mu(E\cap[b]_d)\in\{0\}\cup[\delta_d,p^{-d}],
\qquad
M\ge c_p.
\tag{TM.565}
$$

**Proof.** If an included ancestor or equal-depth cylinder contains $D$, its intersection with $E$ is empty. Otherwise, the nesting property of $p$-adic cylinders implies that every forbidden cylinder meeting $D$ has depth greater than $d$ and lies inside $D$. Consequently,
$$
\mu(E\cap D)
\ge p^{-d}-\sum_{h>d}p^{-h}
=\frac{p-2}{p-1}p^{-d}
=\delta_d.
\tag{TM.566}
$$
Positive mass implies nonemptiness, proving the equivalence. At depth zero there is no permitted forbidden ancestor, giving $M\ge c_p$. $\square$

This criterion and gap are the ordinary mathematical result of [profile 343, §13, snapshot c2258c72](https://github.com/the-omega-institute/trureturing/blob/c2258c72a04890a997f2c5796a64be5a7247c0f9/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md). The derivation uses countable subadditivity and does not require forbidden cylinders to be disjoint or nonredundant.

#### 2.7.2 Computing cylinder masses from the total mass

**引理 2.21（effective localization of mass）。** Let $F\subseteq\mathbb Z_p$ be any effectively closed set, without a sparsity assumption. Given its computable complement enumeration and a rational Cauchy name for $\mu(F)$, the masses $\mu(F\cap[b]_d)$ are uniformly computable in $(d,b)$. Here a rational Cauchy name is a function $v:\mathbb N\to\mathbb Q$ satisfying
$$
|v(t)-\mu(F)|\le2^{-t}.
\tag{TM.567}
$$

**Proof.** Apply C卷第2.3.3节 with alphabet $\{0,\ldots,p-1\}$, $C=F$, its given complement enumeration, and computable Haar measure. Total mass may be zero: this uses only the localization part, not positive-mass selection. In this instance the following exact rational implementation avoids separately computing all $p^d$ cylinder masses. Simulate the complement enumeration for $s$ computation steps. Let $F_s$ be the complement of the finite union of all cylinders announced during that simulation. These are uniformly computable clopen sets with
$$
F_{s+1}\subseteq F_s,
\qquad
\bigcap_sF_s=F,
\qquad
f_s:=\mu(F_s)\downarrow\mu(F).
\tag{TM.568}
$$
Using a finite computation-time stage makes each $F_s$ computable even when no new event arrives. For $D=[b]_d$, put
$$
m=\mu(F\cap D),
\qquad
u_s=\mu(F_s\cap D),
\qquad
\ell_t=v(t)-2^{-t}.
\tag{TM.569}
$$
Finite unions and intersections of $p$-adic cylinders have exactly computable rational masses. Since $F\subseteq F_s$ and $\ell_t\le\mu(F)$,
$$
L_{s,t}
:=\max\{0,\ell_t-(f_s-u_s)\}
\le m\le u_s.
\tag{TM.570}
$$
Indeed, $f_s-u_s$ is the mass of $F_s\setminus D$ in the same probability space and bounds the mass of $F\setminus D$ from above. The interval width satisfies
$$
0\le u_s-L_{s,t}\le f_s-\ell_t.
\tag{TM.571}
$$
Given a positive rational error tolerance $\varepsilon$, choose $t$ with $2^{1-t}<\varepsilon/2$. Then
$$
0\le\mu(F)-\ell_t\le2^{1-t}<\varepsilon/2.
\tag{TM.572}
$$
Search through stages $s$ until the rational inequality $f_s-\ell_t<\varepsilon$ holds. Convergence of $f_s$ guarantees termination. The resulting interval encloses $m$ and has width less than $\varepsilon$. This gives its rational approximations uniformly. $\square$

The generic lemma is owned by C卷第2.3.3节; C卷第2.4.8节 is its three-adic positive-selection application. Its validity does not require $\mu(F)>0$; positivity is needed only for that section's subsequent selection of a positive-mass child. The displayed form computes one cylinder mass using $f_s$ and $u_s$, so it does not require separately evaluating all $p^d$ cylinder masses.

**命题 2.22（total mass decides sparse extendibility）。** Under the sparse hypotheses of C卷第2.7.1节, a rational Cauchy name for $M$ uniformly computes the characteristic function of $R$.

**Proof.** Given $(d,b)$, use the preceding lemma to compute a rational $q$ with
$$
\left|q-\mu(E\cap[b]_d)\right|<\delta_d/3.
\tag{TM.573}
$$
If $(d,b)\notin R$, its cylinder mass is zero and $q<\delta_d/2$. If $(d,b)\in R$, its mass is at least $\delta_d$ and $q>\delta_d/2$. Therefore the rational comparison
$$
(d,b)\in R\quad\Longleftrightarrow\quad q>\delta_d/2
\tag{TM.574}
$$
is decisive; equality cannot occur for such an approximation. $\square$

**Quantitative form.** For this decision, one total-mass-name query at an index $t$ satisfying
$$
2^{-t}<\delta_d/12
\tag{TM.575}
$$
suffices. Set $\ell_t=v(t)-2^{-t}$ and search for $s$ with $f_s-\ell_t<\delta_d/3$. Since $M-\ell_t<\delta_d/6$, this search terminates. The rational $u_s=\mu(E_s\cap[b]_d)$ then satisfies
$$
0\le u_s-\mu(E\cap[b]_d)<\delta_d/3,
\tag{TM.576}
$$
so one may use $q=u_s$ in the decision rule. The required binary accuracy index can be chosen as the least integer strictly larger than
$$
d\log_2p+\log_2(12/c_p).
\tag{TM.577}
$$
This counts a requested accuracy, not the number of enumeration steps or the total running time. The stopping stage $s$, the number and depths of cylinders discovered by that stage, the bit lengths of the name's rational answer, and the exact rational arithmetic remain part of the computational cost. No bound on these costs follows merely from the depth $d$ and the accuracy index $t$.

#### 2.7.3 Extension queries compute mass with an explicit geometric error

**定义 2.23。** Let
$$
R_n=\{b\in\{0,\ldots,p^n-1\}:(n,b)\in R\},
\qquad
B_n=\bigcup_{b\in R_n}[b]_n,
\qquad
a_n=|R_n|p^{-n}=\mu(B_n).
\tag{TM.578}
$$
These are the cylinders extendible in the final set $E$, not the candidates that have merely survived a finite amount of event enumeration.

**命题 2.24（tail bound）。** For every $n\ge0$,
$$
E\subseteq B_n,
\qquad
B_n\setminus E\subseteq\bigcup_{h>n:\,C_h\text{ included}}C_h,
\tag{TM.579}
$$
and hence
$$
0\le a_n-M\le\frac{p^{-n}}{p-1}.
\tag{TM.580}
$$

**Proof.** The depth-$n$ cylinder containing any $x\in E$ intersects $E$, so $x\in B_n$. Conversely, let $x\in B_n\setminus E$, and let $D$ be its depth-$n$ cylinder. Then $E\cap D\ne\varnothing$, while $x$ belongs to some included forbidden cylinder $C_h$. If $h\le n$, the intersecting cylinders are nested with $D\subseteq C_h$, forcing $E\cap D=\varnothing$, a contradiction. Thus $h>n$. This proves the inclusion regardless of overlap or redundancy among the forbidden cylinders. Countable subadditivity now gives
$$
\mu(B_n\setminus E)
\le\sum_{h>n}p^{-h}
=\frac{p^{-n}}{p-1}.
\tag{TM.581}
$$
Because $E\subseteq B_n$, this difference is exactly $a_n-M$. $\square$

**命题 2.25（sparse extendibility computes total mass）。** The characteristic function of $R$ uniformly computes a rational Cauchy name for $M$.

**Proof.** Given a binary accuracy request $m\ge0$, choose the least $n\ge0$ satisfying
$$
\frac{p^{-n}}{p-1}\le2^{-m}.
\tag{TM.582}
$$
Query $(n,b)\in R$ for all $0\le b<p^n$, count the positive answers, and output $a_n$. The tail bound gives $|a_n-M|\le2^{-m}$. $\square$

**Quantitative form.** This procedure uses exactly $p^n$ Boolean extension queries at depth $n$, followed by finite counting and division by $p^n$. For $n\ge1$, minimality of $n$ gives
$$
\frac{2^m}{p-1}\le p^n<\frac{p}{p-1}2^m.
\tag{TM.583}
$$
For $n=0$ it uses one query. A standard representative $b$ needs at most $\lceil n\log_2p\rceil$ binary digits, apart from the representation of the depth itself. Thus the stated query count is generally exponential in the requested number $m$ of binary accuracy bits for this procedure. These are query and representation bounds; they are neither an optimality assertion nor a polynomial-time claim.

**注 2.26。** The reverse tail bound uses the one-cylinder-per-depth condition but not the strict positivity of $c_p$. Its proof also works for $p=2$. It does not provide an effective approximation merely from the event stream: computing the final sets $R_n$ is the oracle operation being assumed.

#### 2.7.4 Uniform oracle equivalence and its representation meaning

**定理 2.27（exact mass and extension queries）。** Fix the computable event presentation and odd prime $p$ from C卷第2.7.1节. For every oracle $A$,
$$
M\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
R\text{ is }A\text{-decidable}.
\tag{TM.584}
$$
Uniformly in the presentation and $p$, there is an operator sending any valid rational Cauchy name of $M$ to the characteristic function of $R$, and an operator sending the characteristic function of $R$ to a rational Cauchy name of $M$. In particular,
$$
M\text{ is computable}
\quad\Longleftrightarrow\quad
R\text{ is decidable}.
\tag{TM.585}
$$

**Proof.** If $M$ has an $A$-computable name, perform the construction of C卷第2.7.2节 using that name and the fixed computable presentation; every required operation is then $A$-computable. If $R$ is $A$-decidable, the finite query procedure of C卷第2.7.3节 returns an $A$-computable rational Cauchy name. These constructions are uniform in the specified inputs. $\square$

**注 2.28。** This theorem does not assert that every arbitrary name of $M$ has exactly the Turing degree of $R$. A valid name can encode additional irrelevant information in its rational approximations. The precise assertion is the oracle-relative computability equivalence and the two uniform operators. The presentation is fixed and computable; if it is instead supplied through another oracle, that access must remain an explicit input to the forward construction.

**推论 2.29（selection）。** Either a decidable $R$ or a computable $M$ suffices to compute one point of $E$.

**Proof.** The root cylinder meets $E$ because $M\ge c_p>0$. From an extendible depth-$n$ cylinder, query its $p$ children and select the least extendible one. At least one exists since the children partition the parent. Iteration computes compatible standard residues of a point in the closed set $E$. By the preceding theorem, a computable mass supplies the same extension decisions. $\square$

The converse from one computable point to computable total mass or decidable extension is false, as C卷第2.7.6节 shows. Decidable extension also need not recover the entire raw inventory: undecidable announcements of redundant descendants inside an already forbidden cylinder leave $E$, its mass, and every extension answer unchanged.

#### 2.7.5 The diagonal survivor set

**定义 2.30。** Use exactly the effective enumeration $(\varphi_e)_{e\ge0}$ fixed in C卷第2.2.1节, with the same Haar law and events, as in [profile 343, §10](https://github.com/the-omega-institute/trureturing/blob/c2258c72a04890a997f2c5796a64be5a7247c0f9/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md). Whenever $\varphi_e(e+1)$ halts with output $a_e$, forbid
$$
[a_e\bmod3^{e+1}]_{e+1}.
\tag{TM.586}
$$
Let $K\subseteq\mathbb Z_3$ be the complement of the resulting union. There is at most one forbidden cylinder at each positive depth. The same construction gives
$$
\mu(K)\ge\frac12,
\qquad
K\text{ contains no computable }3\text{-adic point}.
\tag{TM.587}
$$

**Proof of the stated properties.** These are precisely C卷第2.2.2节 applied to its unchanged set $K$; the depth $e+1$ in (TM.586) is the depth of $C_e$ in (TM.478). No new diagonal construction is being chosen. $\square$

**推论 2.31。** The cylinder-extension relation $R_K$ is undecidable, and $\mu(K)$ is noncomputable. More precisely, for every oracle $A$,
$$
\mu(K)\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
R_K\text{ is }A\text{-decidable}.
\tag{TM.588}
$$

**Proof.** If $R_K$ were decidable, the child-selection construction would give a computable point of $K$. Hence it is undecidable, and the equivalence theorem gives noncomputability of the mass and the relative assertion. $\square$

This recovers the noncomputability conclusion of C卷第2.4.8节 and identifies the equivalent extension-query task under the sparse presentation. Cylinder emptiness has a finite forbidden-ancestor witness, so $R_K$ is co-c.e.; the halting oracle decides it and computes a mass name. No completeness classification of this particular $R_K$ is asserted here.

#### 2.7.6 Hard extension queries with an explicit computable point

**定义 2.32。** Let $A\subseteq\mathbb N$ be co-c.e., and put
$$
D_n=[p^n]_{n+1}\qquad(n\ge0).
\tag{TM.589}
$$
Enumerate $D_n$ as forbidden exactly when $n$ enters the c.e. complement of $A$, and let $E_A$ be the remaining closed set. The cylinders $D_n$ are pairwise disjoint and use exactly one possible cylinder at each positive depth.

**命题 2.33。** The point $0$ belongs to $E_A$, and
$$
E_A\cap D_n=
\begin{cases}
D_n,&n\in A,\\
\varnothing,&n\notin A.
\end{cases}
\tag{TM.590}
$$
The extension relation $R_{E_A}$ is Turing equivalent to $A$, and
$$
\mu(E_A)=1-\sum_{n\notin A}p^{-(n+1)}.
\tag{TM.591}
$$
Consequently $\mu(E_A)$ is computable if and only if $A$ is decidable, although $E_A$ always has the explicit computable point $0$.

**Proof.** In low-to-high digit order, $D_n$ begins with $0^n1$. These prefixes are incompatible for different $n$, proving disjointness, and none contains zero. Thus removing the announced $D_n$ gives the displayed intersections and the exact mass formula. The map $n\mapsto(n+1,p^n)$ reduces membership in $A$ to extension. Conversely, with oracle $A$, decide whether a cylinder $[b]_d$ has an included ancestor by examining only $D_0,\ldots,D_{d-1}$; the sparse ancestor criterion then decides its extension. Hence $R_{E_A}\equiv_T A$. The mass conclusion follows from the oracle-equivalence theorem. $\square$

If $A$ is co-c.e.-complete, every name of $\mu(E_A)$ computes the halting problem through the extension operator, and the halting oracle computes one such name. This statement leaves arbitrary extra information in other names unconstrained. The example is the fixed-inventory construction of profile 343, §13; its computable survivor and its hard extension queries are properties of the same set.

#### 2.7.7 Why general effectively closed sets require different conclusions

**命题 2.34（computable mass without decidable extension）。** For an odd prime $p$, there exists an effectively closed $F\subseteq\mathbb Z_p$ with positive computable mass and an undecidable cylinder-extension relation.

**Proof.** Take a nondecidable co-c.e. set $A$. Let $N$ be the closed set of $p$-adic points all of whose digits belong to $\{0,1\}$. It is effectively closed and has Haar measure zero, since its depth-$n$ cover has mass $(2/p)^n$. Define
$$
N_A=N\setminus\bigcup_{n\notin A}D_n,
\qquad
F=[0]_1\cup(1+pN_A).
\tag{TM.592}
$$
The set $N_A$ is effectively closed and null, and the two displayed components of $F$ lie in disjoint depth-one cylinders. Hence $F$ is effectively closed and $\mu(F)=1/p$. For each $n$, the cylinder $1+pD_n$ meets $F$ if and only if $D_n$ meets $N_A$, which holds exactly when $n\in A$: when allowed, the point $p^n$ belongs to $N\cap D_n$. Thus its extension relation is undecidable. Each queried intersection has mass zero whether empty or nonempty. $\square$

This example shows why computable local masses do not generally decide nonemptiness. The strict gap of C卷第2.7.1节 excludes these nonempty null intersections. There is also a separate obstruction: zero-testing a uniformly computable family of cylinder masses can itself be undecidable.

**命题 2.35（computable total mass with undecidable zero cylinder masses）。** For an odd prime $p$, there is an effectively closed $F\subseteq\mathbb Z_p$ with positive computable total mass and a computable family of cylinders whose intersection masses with $F$ are zero exactly on a nondecidable set.

**Proof.** Enumerate machines with their inputs fixed. Put
$$
q_n=
\begin{cases}
p^{-t},&\text{machine }n\text{ first halts at step }t\ge1,\\
0,&\text{it never halts}.
\end{cases}
\tag{TM.593}
$$
These real numbers are uniformly computable: simulation through $T$ steps either finds the exact value or bounds any later value by $p^{-T}$. Nevertheless $q_n=0$ is the nonhalting predicate.

For $y=\sum_{j\ge0}y_jp^j\in\mathbb Z_p$, define
$$
\theta(y)=\sum_{j\ge0}y_jp^{-(j+1)}\in[0,1].
\tag{TM.594}
$$
This is a computable continuous map. Under Haar measure its digits are independent and uniform, so its pushforward is Lebesgue measure on $[0,1]$. In particular,
$$
\mu\{y:\theta(y)\le q\}=q,
\qquad
\mu\{y:\theta(y)\ge q\}=1-q
\qquad(0\le q\le1).
\tag{TM.595}
$$
Endpoint fibers have measure zero. The two sets are effectively closed uniformly in a computable name for $q$, because the strict reverse inequalities define effectively open preimages.

Inside $D_n=[p^n]_{n+1}$, use its two children with next digit $0$ and $1$:
$$
F_{n,0}=\{p^n+p^{n+2}y:\theta(y)\le q_n\},
\qquad
F_{n,1}=\{p^n+p^{n+1}+p^{n+2}y:\theta(y)\ge q_n\}.
\tag{TM.596}
$$
Put
$$
F=\{0\}\cup\bigcup_{n\ge0}(F_{n,0}\cup F_{n,1}).
\tag{TM.597}
$$
Each component is closed in its clopen cylinder $D_n$, and these cylinders accumulate only at zero, which has been included. The complement is effectively open: outside zero, the first nonzero digit either excludes the point immediately or identifies its unique $D_n$; its next digit and the applicable strict inequality then enumerate the complement inside that cylinder. Thus $F$ is effectively closed. The disjoint pairs have masses
$$
\mu(F_{n,0})=p^{-(n+2)}q_n,
\qquad
\mu(F_{n,1})=p^{-(n+2)}(1-q_n).
\tag{TM.598}
$$
Consequently,
$$
\mu(F)=\sum_{n\ge0}p^{-(n+2)}=\frac1{p(p-1)}.
\tag{TM.599}
$$
For the computable cylinder family $C_n=[p^n]_{n+2}$, its intersection with $F$ is exactly $F_{n,0}$. Therefore
$$
\mu(F\cap C_n)=0
\quad\Longleftrightarrow\quad
q_n=0
\quad\Longleftrightarrow\quad
\text{machine }n\text{ does not halt}.
\tag{TM.600}
$$
This proves undecidability of zero cylinder mass despite computability of the total mass and of every local mass uniformly. $\square$

Neither general example is asserted to admit the one-forbidden-cylinder-per-depth presentation of C卷第2.7.1节. The equivalence theorem depends on that structural promise, not merely on effective closedness or positive total mass.

#### 2.7.8 Binary and finite-cover boundaries

For $p=2$, the ancestor estimate gives only
$$
p^{-d}-\sum_{h>d}p^{-h}=0.
\tag{TM.601}
$$
Thus the positive gap used to turn a local mass approximation into an extension decision disappears. A concrete binary example forbids $[2^n]_{n+1}$ for every $n\ge0$: the complement is the singleton $\{0\}$, so its root cylinder is extendible while its mass is zero. The reverse geometric tail bound remains valid, and the localization lemma remains valid. The failure of this positive-gap proof does not assert that no other binary criterion or implication is possible.

All equivalences here concern an infinite, fixed, effectively presented inventory and exact Haar mass as a real number. Finite-stage candidate counts do not determine the final extension sets without an additional oracle or a termination guarantee for the relevant absence questions. A supplied finite congruence family remains decidable by checking a finite common period. No reduction to the finite distinct odd covering problem, solution of that problem, formal independence statement, or research-priority claim follows from these results.

### 2.8 Sparse binary exclusions: pointwise mass equivalence and failure of uniform transport

Fix the native binary prefix tower, with digits read from low to high in $\mathbb Z_2$. This section completes the binary boundary of C卷第2.7节. It uses the canonical-cylinder result of C卷第2.6节. The statements below are ordinary mathematical proofs; they assert neither Lean verification nor research originality. They concern effectively presented infinite families and do not settle a finite covering conjecture.

#### 2.8.1 Presentation, extension, and canonical forbidden depths

For a finite binary word $s$, write $[s]$ for its clopen cylinder in

$$
X=\{0,1\}^{\mathbb N}\cong\mathbb Z_2,
\qquad \mu([s])=2^{-|s|}.
\tag{TM.652}
$$

The root is the empty word and has depth zero. Fix a computably enumerable event presentation $\mathcal P$ containing at most one final forbidden cylinder at each positive depth. Repeated announcements of that same cylinder are harmless. No depth-zero cylinder is permitted, and a small-depth event may arrive arbitrarily late. Set

$$
U=\bigcup_{C\in\mathcal P}C,
\qquad E=X\setminus U,
\qquad M=\mu(E),
\qquad R=\{s:E\cap[s]\ne\varnothing\}.
\tag{TM.653}
$$

The final complement $E$ is effectively closed. The depth restriction implies $U\ne X$: if the cylinders covered the compact space $X$, some finite subfamily would cover it, while for any finite set $F$ of positive depths,

$$
\mu\left(\bigcup_{h\in F}C_h\right)
\le\sum_{h\in F}2^{-h}<1.
\tag{TM.654}
$$

Thus $E$ is always nonempty, including when $M=0$.

Let $\mathcal B$ be the canonical shortest forbidden-prefix basis,

$$
\mathcal B
=\{[s]: |s|\ge1,\ [s]\subseteq U,\ [s^-]\not\subseteq U\},
\tag{TM.655}
$$

where $s^-$ deletes the last digit. These cylinders are pairwise disjoint and cover $U$. Define their depth support

$$
S=\{h\ge1:\text{some }[s]\in\mathcal B\text{ has }|s|=h\}.
\tag{TM.656}
$$

**命题 2.36。** Every member of $\mathcal B$ is an actual member of $\mathcal P$. Consequently $\mathcal B$ contains at most one cylinder at each depth.

**Proof.** Apply C卷第2.6.2节 to the native binary prefix tower, with $p=2$, the same open set $U$, and the presentation $\mathcal P$ as its distinct-depth generating family. The canonical basis there is exactly $\mathcal B$. Its compactness argument uses the strict finite bound

$$
\sum_{i=1}^k2^{-r_i}\le\sum_{r=1}^{\max_i r_i}2^{-r}<1,
\tag{TM.657}
$$

and therefore includes the binary endpoint even though the infinite tail sum equals one. It gives actual membership of every canonical cylinder in this very presentation. $\square$

Write $B_h$ for the unique canonical cylinder at any depth $h\in S$. Pairwise disjointness gives

$$
\boxed{1-M=\mu(U)=\sum_{h\in S}2^{-h}.}
\tag{TM.658}
$$

This is an equality for the canonical basis. Summing the raw event inventory instead can overcount redundant descendants.

#### 2.8.2 The canonical depth support and extension have the same oracle information

**命题 2.37。** For the fixed computable presentation $\mathcal P$,

$$
R\equiv_T S.
\tag{TM.659}
$$

The reduction from $S$ to $R$ is uniform when the presentation is also supplied. The reverse reduction does not need that presentation.

**Proof, from $S$ to $R$.** On input a word $s$ of depth $d$, determine the finite set

$$
S\cap\{1,\ldots,d\}.
\tag{TM.660}
$$

For every depth $h$ in this set, simulate the event presentation until its unique depth-$h$ cylinder is announced. These finitely many waits all terminate because $B_h$ is a raw member. Return that $s\notin R$ exactly when one of these cylinders contains $[s]$.

To check completeness of this test, if $s\notin R$ then $[s]\subseteq U$. Along the finite chain of ancestors of $[s]$, choose the shortest one contained in $U$. Since $U\ne X$, its depth is positive and at most $d$. It is canonical and therefore appears in the finite list used by the procedure. Conversely, any such forbidden ancestor plainly makes $[s]$ disjoint from $E$. The empty word is always extendible.

**Proof, from $R$ to $S$.** For each $h\ge1$, inspect the finitely many words $s$ of length $h$. The condition

$$
[s]\in\mathcal B
\quad\Longleftrightarrow\quad
s\notin R\ \text{and}\ s^-\in R
\tag{TM.661}
$$

decides whether a canonical cylinder exists at that depth. Therefore it decides membership of $h$ in $S$. $\square$

The first procedure needs to discover at most $d$ raw cylinders for a depth-$d$ query. The theorem provides no bound on how long their announcements may be delayed.

#### 2.8.3 A binary expansion lemma, including dyadic ambiguity

Put $r=1-M$. The preceding mass identity presents $r$ as a binary series whose digit at depth $h$ is $\mathbf 1_S(h)$.

**引理 2.38。** For every oracle $A$ and every set $S\subseteq\mathbb N_{>0}$,

$$
\sum_{h\in S}2^{-h}\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
S\text{ is }A\text{-decidable}.
\tag{TM.662}
$$

This is an oracle-relative, pointwise statement. There is no uniform operator that, from a name of the sum alone, selects the original set $S$ for all inputs.

**Proof of the reverse implication.** The finite partial sum through depth $n$ has error at most

$$
\sum_{h>n}2^{-h}=2^{-n},
\tag{TM.663}
$$

so an $A$-decision procedure for $S$ computes the real uniformly.

**Proof of the forward implication when $r$ is nondyadic.** For every $n$, the real $r$ lies strictly between two consecutive points of the grid $2^{-n}\mathbb Z$. From an $A$-computable Cauchy name, search for an approximation interval that lies entirely within one such open interval. The search terminates because $r$ is not a grid point. Its interval index determines the first $n$ binary digits, which uniquely equal the first $n$ digits of $\mathbf 1_S$. This computes $S$ relative to $A$.

**Proof of the forward implication when $r$ is dyadic.** Every binary expansion of a dyadic real in $[0,1]$ is either eventually zero or eventually one. Hence $S$ is finite or cofinite and is computable without any oracle.

For completeness, the ambiguity statement follows by comparing two digit sequences at their first unequal index $j$. A difference of $2^{-j}$ there can be canceled by the later digits only if their entire tail difference attains

$$
\sum_{h>j}2^{-h}=2^{-j}.
\tag{TM.664}
$$

Equality forces every later digit on one side to be zero and every later digit on the other to be one. Comparing with a terminating expansion proves the stated dyadic alternatives. At $r=0$ the only support is empty, and at $r=1$ it is all positive depths. $\square$

In the dyadic case, the statement that a finite or cofinite set is computable is nonuniform: a program may contain its finite exceptional set as constants. It does not give a procedure recovering those constants, or choosing between the two binary expansions, from an arbitrary real name. The pointwise theorem does not use such a procedure.

#### 2.8.4 Pointwise binary mass–extension equivalence

**定理 2.39。** Fix a computable event presentation with at most one forbidden binary cylinder per positive depth. For every oracle $A$,

$$
\boxed{
M\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
R\text{ is }A\text{-decidable}.
}
\tag{TM.665}
$$

In particular,

$$
M\text{ is computable}
\quad\Longleftrightarrow\quad
R\text{ is decidable}.
\tag{TM.666}
$$

**Proof.** Subtracting from one preserves computability of a real. The binary expansion lemma identifies computability of $1-M$ with decidability of the canonical depth support $S$. The reductions in C卷第2.8.2节 identify decidability of $S$ with decidability of $R$. Every reduction uses the same fixed presentation and the same final complement. $\square$

For a nondyadic mass, the forward construction is uniform in the presentation and a valid mass name, under that nondyadic promise. For a dyadic mass, $R$ is decidable outright, but the proof is nonuniform in the presentation. Thus every fixed presentation admits a mass-name-to-extension operator, while one common such operator for all presentations need not exist. The next section proves that it does not exist.

The reverse direction remains uniform over all permitted presentations, including dyadic ones. Define

$$
R_n=\{s\in\{0,1\}^n:s\in R\},
\qquad
A_n=\bigcup_{s\in R_n}[s],
\qquad a_n=|R_n|2^{-n}.
\tag{TM.667}
$$

Then

$$
E\subseteq A_n,
\qquad
A_n\setminus E\subseteq\bigcup_{h>n:\,C_h\text{ announced}}C_h,
\tag{TM.668}
$$

because any forbidden ancestor of depth at most $n$ would make the containing depth-$n$ cylinder nonextendible. Therefore

$$
\boxed{0\le a_n-M\le2^{-n}.}
\tag{TM.669}
$$

An extension oracle computes a $2^{-n}$-accurate rational approximation by $2^n$ depth-$n$ queries. This is a bound for the displayed procedure, not an optimality claim.

**Zero-mass endpoint.** If $M=0$, then $S$ contains every positive depth. The first $n$ canonical cylinders are disjoint, have total mass $1-2^{-n}$, and are unions of depth-$n$ cylinders. Exactly one depth-$n$ cylinder remains. These remaining cylinders form a nested sequence, whose intersection is a single point. The raw enumeration effectively supplies the first $n$ canonical cylinders, so this point is computable. Thus every zero-mass complement in this sparse binary class is a computable singleton. General effectively closed null sets do not satisfy this restriction.

#### 2.8.5 Constant mass does not support a uniform extension algorithm

**定理 2.40。** There is a uniformly computable family of permitted event presentations, all with complement mass $1/2$, for which one cylinder-extension query is the nonhalting predicate. Consequently no total uniform operator can take a permitted presentation and a valid name of its mass and return its extension characteristic function.

**Proof.** For each machine index $e$, always enumerate

$$
[01],\ [001],\ [0001],\ldots,
\quad\text{equivalently }[0^n1]\ (n\ge1).
\tag{TM.670}
$$

Independently simulate machine $e$ on its specified input. If it halts, enumerate $[0]$. Dovetail these two procedures. There is one possible forbidden cylinder at depth one and exactly one at each depth at least two, so the sparsity condition holds for every $e$, with no promise about halting.

The cylinders $[0^n1]$ cover $[0]\setminus\{0^\infty\}$. Hence the final complements are

$$
E_e=
\begin{cases}
[1],&e\text{ halts},\\
[1]\cup\{0^\infty\},&e\text{ does not halt}.
\end{cases}
\tag{TM.671}
$$

In both cases,

$$
\mu(E_e)=\frac12,
\tag{TM.672}
$$

but

$$
E_e\cap[0]\ne\varnothing
\quad\Longleftrightarrow\quad
e\text{ does not halt}.
\tag{TM.673}
$$

If the asserted uniform operator existed, provide it with this effectively constructed presentation index and the constant rational Cauchy name $v(t)=1/2$. Querying the returned extension procedure at $[0]$ would decide nonhalting, a contradiction. $\square$

Every individual $R_{E_e}$ is nevertheless decidable. In the halting case it is the extension relation of $[1]$. In the nonhalting case a finite word is extendible exactly when it is empty, begins with $1$, or consists only of zeros. The impossibility concerns uniformly selecting the correct procedure from $e$ and the identical mass name.

The canonical supports display the ambiguity directly:

$$
S_e=
\begin{cases}
\{1\},&e\text{ halts},\\
\{2,3,4,\ldots\},&e\text{ does not halt}.
\end{cases}
\tag{TM.674}
$$

They encode the same forbidden mass through

$$
\frac12=2^{-1}=\sum_{h=2}^{\infty}2^{-h}.
\tag{TM.675}
$$

The raw event list does not resolve this alternative at a bounded stage: an announcement of $[0]$ may still arrive later. No claim of a computable stabilization bound is used.

#### 2.8.6 What the binary endpoint changes

For an odd prime $p$, the sparse cylinder lower bound

$$
\mu(E\cap[s])\in\{0\}\cup
\left[\frac{p-2}{p-1}p^{-|s|},\ p^{-|s|}\right]
\tag{TM.676}
$$

provides a uniform positive separation and therefore a uniform mass-name-to-extension operator. At $p=2$, that lower gap vanishes. The pointwise equivalence survives by canonical binary expansion, but uniform transport over all presentations fails.

The distinction can be recorded without treating one as the other:

$$
\begin{aligned}
&\text{Fixed sparse binary presentation:}&&
M\text{ is }A\text{-computable}\iff R\text{ is }A\text{-decidable};\\
&\text{Uniform over sparse binary presentations:}&&
R\longmapsto M\text{ is computable};\\
&&&(
\mathcal P,\text{name}(M))\longmapsto R
\text{ is not computable in general}.
\end{aligned}
\tag{TM.677}
$$

A dyadic mass supplied with its exact rational value and the choice of terminating versus eventually-one canonical support is enough finite advice to make the forward construction uniform on that subclass. For nondyadic inputs, the usual digit-extraction search already gives a uniform construction, but its stopping precision has no bound here depending only on the requested depth: the real may lie arbitrarily close to a dyadic boundary.

These are statements about effective access to one fixed final object and its specified prefix interface. They do not identify arbitrary real names with a unique Turing degree: a name may carry unrelated extra information. They also do not infer the raw redundant inventory from extension, or equate existence of a decision program with a uniform means of obtaining that program. In particular, the constant-mass family shows exactly why those two claims cannot be interchanged.

### 2.9 变量进制的稀疏延拓与统一性

本节将C卷第2.7节的奇素数幂稀疏模型、C卷第2.8节的二进制点态等价与统一性反例，以及C卷第2.6节的规范柱定理扩展到球对称的可计算变量进制树。下面保留变权重、精确尾隙和最终二进尾的全部适配证明；这些是普通数学推导，不主张新增 Lean 核验、原创性或有限覆盖问题的结算。

#### 2.9.1 The common tree, probability law, and event presentation

Fix a computable sequence of integers

$$
b_n\ge2\qquad(n\ge1),
\qquad B_0=1,
\qquad B_n=\prod_{i=1}^n b_i,
\qquad w_n=B_n^{-1}.
$$

The ambient space and its probability law are

$$
X=\prod_{n\ge1}\{0,1,\ldots,b_n-1\},
\qquad
\mu=\bigotimes_{n\ge1}\operatorname{Unif}\{0,\ldots,b_n-1\}.
$$

A finite word $s=(s_1,\ldots,s_d)$ with $0\le s_i<b_i$ defines a depth-$d$ cylinder $[s]$, with

$$
\mu([s])=w_d.
$$

The root has depth zero and mass one. The term *spherically symmetric* means that every node at a given depth has the same number of children, regardless of its earlier digits. No arithmetic primality assumption is imposed on $b_n$.

Fix a computably enumerable presentation $\mathcal P$ that contains at most one final forbidden cylinder at every positive depth. Repetition of the same announcement is allowed; competing cylinders at the same depth are not. The root is not permitted as a forbidden cylinder. Define

$$
U=\bigcup_{C\in\mathcal P}C,
\qquad
E=X\setminus U,
\qquad
M=\mu(E),
\qquad
R=\{s:E\cap[s]\ne\varnothing\}.
$$

All objects refer to this one final event inventory and this one product measure. A small-depth event may arrive arbitrarily late.

Since $b_n\ge2$,

$$
w_{d+r}\le2^{-r}w_d,
\qquad
\sum_{r=1}^{N}w_{d+r}
\le w_d(1-2^{-N})<w_d.
$$

Consequently $U\ne X$. Otherwise compactness would yield a finite subcover, whose distinct positive depths give total mass strictly below one. In particular, every permitted complement $E$ is nonempty, although its mass may be zero in the all-binary case.

#### 2.9.2 Canonical cylinders and the exact extension relation

Let

$$
\mathcal B
=\{[s]: |s|\ge1,\ [s]\subseteq U,\ [s^-]\not\subseteq U\}
$$

be the canonical shortest forbidden-prefix basis. Here $s^-$ deletes the last symbol. These cylinders are pairwise disjoint and cover $U$.

**命题 2.41。** Every member of $\mathcal B$ occurs in the raw presentation $\mathcal P$. Thus $\mathcal B$ contains at most one cylinder at each depth.

**Proof.** Suppose a canonical cylinder $D$ at depth $d$ is absent from the presentation. Any raw cylinder meeting it must be contained in it: a strict raw ancestor would contradict its canonical minimality. Thus the raw cylinders meeting $D$ are proper descendants and cover $D$. Compactness supplies a finite subcover. If $N$ is the largest relative depth used, its total mass is at most

$$
\sum_{r=1}^{N}w_{d+r}<w_d=\mu(D),
$$

contradicting that it covers $D$. $\square$

The same argument gives an ancestor criterion without any positive-mass assumption:

$$
\boxed{
E\cap[s]\ne\varnothing
\quad\Longleftrightarrow\quad
\text{no announced forbidden cylinder of depth at most }|s|
\text{ contains }[s].
}
$$

Indeed, if $[s]$ were covered with no forbidden ancestor, compactness and the same strict finite-descendant bound would give a contradiction. This is a final-inventory criterion. It does not turn the absence of a future announcement into a decidable event.

Let

$$
S=\{n\ge1:\mathcal B\text{ contains a depth-}n\text{ cylinder}\}.
$$

Disjointness gives the canonical mass identity

$$
\boxed{1-M=\sum_{n\in S}w_n.}
$$

Raw redundant descendants must not be counted a second time in this sum.

**命题 2.42。** For this fixed computable presentation,

$$
R\equiv_T S.
$$

The reduction from $S$ to $R$ is uniform in the presentation. The reverse reduction is independent of the presentation.

**Proof.** Given a depth-$d$ word $s$ and an oracle deciding $S$, find the finitely many canonical depths in $S\cap\{1,\ldots,d\}$. Wait for the raw cylinder at each of these depths. Every wait terminates, because each canonical cylinder is a raw member. The word $s$ is nonextendible precisely when one of these finitely many cylinders is its ancestor. Conversely, using an extension oracle, inspect all words $s$ of depth $n$ and test

$$
[s]\in\mathcal B
\quad\Longleftrightarrow\quad
s\notin R\ \text{and}\ s^-\in R.
$$

This finite search decides whether $n\in S$. $\square$

No time bound for the arrival of the relevant canonical cylinders is implied.

#### 2.9.3 The exact tail gap and its effective witnesses

Define

$$
t_d=\sum_{n>d}w_n,
\qquad
\delta_d=w_d-t_d.
$$

These reals are computable uniformly in $d$ and the radix sequence. For example, truncating $t_d$ at depth $N\ge d$ leaves error at most $w_N\le2^{-N}$. They satisfy

$$
0\le t_d\le w_d,
\qquad 0\le\delta_d\le w_d.
$$

There is also an exact identity:

$$
\boxed{
\delta_d=\sum_{j>d}(b_j-2)w_j.
}
$$

To prove it, use $b_jw_j=w_{j-1}$ and telescope:

$$
\begin{aligned}
\sum_{j=d+1}^{N}(b_j-2)w_j
&=\sum_{j=d+1}^{N}(w_{j-1}-2w_j)\\
&=w_d-\sum_{j=d+1}^{N-1}w_j-2w_N.
\end{aligned}
$$

Letting $N$ tend to infinity gives the identity. All summands are nonnegative. It follows that

$$
\boxed{
\delta_d>0
\quad\Longleftrightarrow\quad
\exists j>d:\ b_j>2.
}
$$

In particular, the immediate next radix $b_{d+1}$ counts. Finding any such index $j$ gives the explicit positive rational lower bound

$$
g_d=(b_j-2)w_j\le\delta_d.
$$

For a depth-$d$ cylinder $D$ with no forbidden ancestor, every forbidden cylinder meeting it is a proper descendant. Therefore

$$
\mu(E\cap D)\ge w_d-\sum_{n>d}w_n=\delta_d.
$$

Together with the ancestor criterion, this gives

$$
\delta_d>0
\quad\Longrightarrow\quad
\mu(E\cap D)\in\{0\}\cup[\delta_d,w_d],
$$

where nonemptiness is equivalent to the second alternative. If $\delta_d=0$, nonemptiness still follows from the ancestor criterion, but a nonempty intersection may be null.

#### 2.9.4 Weighted binary supports and the only possible ambiguity

For any support $S\subseteq\mathbb N_{>0}$, define

$$
F(S)=\sum_{n\in S}w_n.
$$

This is a binary choice of whether to use each weight, even when the ambient radices exceed two.

**引理 2.43（complete ambiguity criterion）。** Suppose $S\ne S'$ and $j$ is their first differing depth. After exchanging the two supports if necessary, take $j\in S$ and $j\notin S'$. Then

$$
F(S)=F(S')
$$

holds if and only if all three conditions hold:

- $b_n=2$ for every $n>j$;
- no $n>j$ belongs to $S$;
- every $n>j$ belongs to $S'$.

**Proof.** Equality forces

$$
w_j
=\sum_{n>j}(\mathbf1_{S'}(n)-\mathbf1_S(n))w_n
\le\sum_{n>j}w_n
=t_j\le w_j.
$$

All inequalities must be equalities. Equality $t_j=w_j$ is equivalent to the first condition by C卷第2.9.3节. Equality in the termwise tail bound requires every tail difference to equal one, yielding the last two conditions. Conversely, these three conditions give cancellation of $w_j$ by the full binary tail. $\square$

Hence a value with more than one support expansion has exactly the familiar terminating-versus-full-tail ambiguity after a finite common prefix. Every participating support is finite or cofinite. In mixed radices the ambiguous real need not be a dyadic rational in the ordinary binary coordinate.

**引理 2.44（effective extraction under unique expansion）。** Given the computable radix sequence and a Cauchy name for $r=F(S)$, the support $S$ can be extracted uniformly whenever this expansion is unique.

Here uniqueness is among all numerical $0/1$ support expansions for these weights, not merely among supports compatible with a particular event inventory. An alternative numerical expansion need not be realizable by that same inventory.

**Proof.** Suppose its digits through depth $n-1$ have been computed. Let

$$
y_n=r-\sum_{j<n}\mathbf1_S(j)w_j.
$$

The two digit possibilities satisfy

$$
\mathbf1_S(n)=0\Longrightarrow y_n\le t_n,
\qquad
\mathbf1_S(n)=1\Longrightarrow y_n\ge w_n.
$$

Dovetail the strict real comparisons

$$
y_n<w_n\quad\text{and}\quad y_n>t_n.
$$

The first certifies digit zero, and the second certifies digit one. Such comparisons are semidecidable from Cauchy names. For a valid expansion they cannot both hold. If neither holds, then necessarily

$$
t_n=w_n=y_n,
$$

which supplies the two alternative support expansions from the ambiguity lemma. Under uniqueness this is excluded, so one comparison eventually succeeds. Proceed inductively. $\square$

The search does not decide whether the radix sequence is eventually binary and does not ask for its last nonbinary index.

**定理 2.45（pointwise support computability）。** For every oracle $A$ and every support $S$,

$$
\boxed{
F(S)\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
S\text{ is }A\text{-decidable}.
}
$$

**Proof.** If $S$ is $A$-decidable, its finite partial sums approximate $F(S)$ with error at most $w_n\le2^{-n}$. Conversely, if the expansion is unique, apply the extraction procedure relative to $A$. If it is ambiguous, the actual support $S$ is finite or cofinite and is therefore computable without an oracle. This latter assertion is nonuniform: the appropriate finite prefix and tail choice can be constants in a program. No procedure selecting them from the real name has been asserted. $\square$

This proof establishes the pointwise statement directly, without giving an algorithm a final-exception index for the radix sequence.

#### 2.9.5 Pointwise mass–extension equivalence for every computable radix sequence

**定理 2.46。** For every fixed computable radix sequence and every fixed computably enumerable sparse presentation as in C卷第2.9.1节, and for every oracle $A$,

$$
\boxed{
M\text{ is }A\text{-computable}
\quad\Longleftrightarrow\quad
R\text{ is }A\text{-decidable}.
}
$$

**Proof.** The canonical identity $1-M=F(S)$ and the support theorem equate computability of $M$ with decidability of $S$. Proposition C卷第2.9.2节 equates decidability of $S$ with decidability of $R$. All statements use the same presentation. $\square$

For each fixed presentation, there exists a functional that computes its extension characteristic function from every valid Cauchy name of its mass. At an ambiguous support value, that functional may instead hardcode the actual finite or cofinite support and ignore the mass input. The existence of this functional does not supply its index uniformly from presentation indices.

One can alternatively prove the eventual-binary case by choosing a finite depth $d$ after the last nonbinary radix and setting

$$
\beta=
\frac{1-M-\sum_{n\le d,\ n\in S}w_n}{w_d}
=\sum_{r\ge1}\mathbf1_S(d+r)2^{-r}.
$$

Its binary digits determine the tail except for the terminating/full-tail ambiguity. Here $d$ and the actual finite prefix support are nonuniform constants, and the dyadic test concerns $\beta$, not the global mass $M$. The preceding proof avoids requiring an algorithm to find either constant.

#### 2.9.6 Uniform recovery when nonbinary levels continue indefinitely

Assume

$$
\forall d\ \exists j>d:\ b_j>2.
$$

There are two uniform constructions of extension from the presentation and a mass name.

First, every $\delta_n$ is positive, so the weighted support expansion is unique. The strict-comparison procedure of C卷第2.9.4节 computes $S$, and the raw-cylinder search of C卷第2.9.2节 computes $R$.

Second, a local mass argument provides an explicit positive-gap certificate. On a depth-$d$ query, search for the first later $j$ with $b_j>2$, and set $g_d=(b_j-2)w_j>0$. This search terminates under the displayed promise. Let $E_s$ be the complement of all forbidden events seen in the first $s$ computation steps, and put

$$
f_s=\mu(E_s),
\qquad u_s=\mu(E_s\cap D),
\qquad \ell_t=v(t)-2^{-t},
$$

where $v$ is a mass name satisfying $|v(t)-M|\le2^{-t}$. Finite unions of cylinders have exactly computable rational mass, and

$$
f_s\downarrow M,
\qquad
\max\{0,\ell_t-(f_s-u_s)\}
\le\mu(E\cap D)\le u_s.
$$

The enclosing interval has width at most $f_s-\ell_t$. Choose $t$ with $2^{-t}<g_d/12$ and wait until

$$
f_s-\ell_t<g_d/3.
$$

Since $M-\ell_t<g_d/6$, this wait terminates. If $D$ is nonextendible, then $u_s<g_d/3$. If $D$ is extendible, then $u_s\ge\mu(E\cap D)\ge g_d$. Comparing $u_s$ with $g_d/2$ therefore decides extension.

This construction is uniform even when a computable radix index is supplied as input, provided the infinite-nonbinary-level promise holds. It does not decide whether that promise holds. It also does not bound the event waiting time. The next nonbinary level may be very distant, and its associated mass $g_d$ may require high precision; neither cost has a uniform bound here depending only on $d$ across all computable radix sequences.

#### 2.9.7 Eventual binary tails obstruct presentation-uniform recovery

Suppose instead that some finite depth $d\ge0$ satisfies

$$
b_n=2\qquad(n>d).
$$

Fix one cylinder $C=[c]$ of depth $d$, using $C=X$ if $d=0$. Its tail is the full binary digit space. Apply C卷第2.8.5节 under the tail embedding $y\mapsto cy$: normalized tail measure becomes $w_d$ times binary Haar measure, the queried cylinder $[0]$ becomes $[c0]$, and depths are shifted by $d$. The formulas below verify these changed measure and depth contracts. For each machine index $e$, construct a uniformly computable event presentation that always announces

$$
[c0^n1]\qquad(n\ge1)
$$

and additionally announces $[c0]$ if machine $e$ halts on its specified input. The announced depths are respectively $d+n+1$ and $d+1$, so every depth has at most one forbidden cylinder.

The unconditional cylinders cover $[c0]\setminus\{c0^\infty\}$. Therefore

$$
E_e=
\begin{cases}
X\setminus[c0],&e\text{ halts},\\
(X\setminus[c0])\cup\{c0^\infty\},&e\text{ does not halt},
\end{cases}
$$

and in both cases

$$
\boxed{M_e=1-\frac{w_d}{2}.}
$$

However,

$$
[c0]\in R_{E_e}
\quad\Longleftrightarrow\quad
e\text{ does not halt}.
$$

If a single algorithm uniformly recovered $R$ from every permitted presentation and a valid mass name, applying it to this family and the same constant rational mass name would decide nonhalting. This is impossible. The counterexample uses one fixed radix sequence and satisfies the presentation restriction for every index $e$ without a halting promise.

The construction uses one fixed finite choice of $d$ to prove nonexistence of a uniform operator for that fixed radix sequence. It does not claim that a program can find $d$ from an arbitrary index for an eventually-binary sequence. Each individual $R_{E_e}$ is decidable by its corresponding explicit formula, so this does not contradict the pointwise theorem.

**Mixed-radix endpoint check.** Take $b_1=3$ and $b_n=2$ for $n\ge2$. Then

$$
w_1=\frac13,
\qquad
\delta_0=\frac13,
\qquad
\delta_1=0.
$$

Embed the construction in $C=[0]$. Its constant mass is

$$
M_e=1-\frac16=\frac56,
$$

which is not dyadic in ordinary binary notation. The query $[00]$ still decides nonhalting. Thus a global positive gap at the root, positive computable total mass, and even a globally nondyadic mass do not provide a uniform decision procedure for every deeper extension query. This exact example checks both the immediate-next-level indexing in C卷第2.9.3节 and the need to normalize any binary-tail test.

**Uniformity classification.** For a fixed computable radix sequence, the following conditions are equivalent:

$$
\begin{aligned}
&b_n>2\text{ at infinitely many levels};\\
&\delta_d>0\text{ at every finite depth};\\
&F:\{0,1\}^{\mathbb N_{>0}}\to\mathbb R
\text{ is injective};\\
&\text{a uniform operator recovers }R
\text{ from every permitted presentation and a mass name}.
\end{aligned}
$$

The first two equivalences follow from the gap identity and ambiguity criterion. The forward algorithm is C卷第2.9.6节, and C卷第2.9.7节 excludes the last property whenever the first fails. This is a mathematical classification, not an algorithm deciding the infinite-level condition from a radix program.

#### 2.9.8 Uniform reverse recovery, resource boundaries, and scope

For every permitted radix sequence, let $R_n$ be the extendible words at depth $n$ and let

$$
A_n=\bigcup_{s\in R_n}[s],
\qquad a_n=|R_n|w_n.
$$

Then

$$
E\subseteq A_n,
\qquad
A_n\setminus E
\subseteq\bigcup_{h>n:\,C_h\in\mathcal P}C_h.
$$

The second inclusion holds because a forbidden ancestor at depth at most $n$ would make the depth-$n$ cylinder nonextendible. Hence

$$
\boxed{
0\le a_n-M\le\sum_{h>n}w_h\le w_n\le2^{-n}.
}
$$

Thus an extension oracle uniformly computes a mass name: choose $n$ with $w_n\le2^{-m}$, query every depth-$n$ word, and return $a_n$. The displayed procedure uses $B_n$ Boolean extension queries. With unbounded computable radices, $B_n$ can overshoot $2^m$ by an arbitrarily large factor; no complexity bound for the radix program or polynomial-time bound is asserted. Taking $n=m$ is always sufficient for correctness, though not necessarily economical.

The forward constructions separately consume radix computation, real-accuracy queries, raw-event waiting, and exact finite rational arithmetic. Pointwise computability does not identify any of these costs. The two-sided oracle statements also do not assign one Turing degree to all real names: a valid name may carry irrelevant extra information.

The spherical and uniform-product hypotheses are essential to the stated reduction to one depth weight. In a general constrained symbolic tree, different nodes at the same depth can have different continuation sets, branching numbers, or cylinder masses. In particular, the legal-word trees for Zeckendorf or $k$-bonacci numeration are not automatically instances of this model: an extension would need to supply the appropriate measure, node-dependent weights, canonical-cylinder conditions, and ambiguity analysis. This section makes no such transfer.

### 2.10 条件幸存、平均递推与随机输出

#### 2.10.1 共同对象与两种索引

沿用C卷第2.2.1节唯一固定的 $X=\mathbb Z_3$、程序枚举 $(\varphi_e)$、事件顺序与归一化 Haar 律 $\mu$。本节的 $K$ 就是式（TM.479）的最终剩余集；C卷第2.2.2节给出

$$
M:=\mu(K)\ge\frac12,\qquad K\text{ 闭且没有可计算点}.
$$

这些构造及有效呈示的区别见 [profile343，第 10、13 节，固定提交 c2258c72a04890a997f2c5796a64be5a7247c0f9](https://github.com/the-omega-institute/trureturing/blob/c2258c72a04890a997f2c5796a64be5a7247c0f9/docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md)。

记

$$
K_0\supseteq K_1\supseteq K_2\supseteq\cdots,
\qquad \bigcap_s K_s=K,
\qquad p_s=\mu(K_s)\downarrow M.
$$

这里 $K_s$ 固定为C卷第2.2.1节算法完成计算阶段 $s$ 后的剩余集：对 $e<s$ 模拟 $s$ 步后，排除已发现禁柱；$K_0=X$。因此它与C卷第2.2.3节的 $q_s^{-1}(H_s)$ 相同，但计算阶段 $s$ 与被查询的前缀深度 $n$ 始终分别索引。因此每个 $K_s$ 都是可计算的 clopen 集，$p_s$ 为可精确计算的有理数，并且

$$
\frac12\le M\le p_s\le1.
$$

$s$ 是约束公布的计算阶段；$n$ 是三进前缀深度。两者是不同参数。仅将二者都编号为自然数，不会使约束更新与前缀细化成为同一种操作。

Bienvenu–Porter 的 [*Deep $\Pi^0_1$ Classes*, arXiv:1403.0450v3，第 11 页 Lemma 3.5](https://arxiv.org/pdf/1403.0450v3) 明确标作 folklore 的引理说明：有效闭集对可计算概率律若有正的可计算质量，便含有可计算点。它的有限字母适配适用于 Haar 三进数字空间。因此 $M$ 不可计算；否则与 $K$ 没有可计算点矛盾。特别地，每个可计算有理数 $p_s$ 都严格大于 $M$。

#### 2.10.2 固定阶段的平均递推与新增约束的缺陷

对 $0\le c<3^n$，写

$$
D_n(c)=[c]_n=c+3^n\mathbb Z_3,
\qquad c^{(j)}=c+j3^n\quad(j=0,1,2).
$$

三个 $D_{n+1}(c^{(j)})$ 分割 $D_n(c)$，Haar 条件权重均为 $1/3$。定义

$$
q_{n,s}(c)
=\mu(K_s\mid D_n(c))
=3^n\mu(K_s\cap D_n(c)).
$$

这个量对所有有限 $n,s$ 都可计算，且为有理数。若只采用 $s\ge n$ 的三角索引区，下面同时使用子层的等式须满足 $s\ge n+1$。

对同一个固定阶段 $s$，有精确平均递推

$$
q_{n,s}(c)
=\frac13\sum_{j=0}^{2}q_{n+1,s}(c^{(j)}).
$$

这是同一事件 $K_s$ 在一个有限分割上的全概率公式。若同时公布新约束，则正确公式为

$$
q_{n,s}(c)
-\frac13\sum_{j=0}^{2}q_{n+1,s+1}(c^{(j)})
=\mu(K_s\setminus K_{s+1}\mid D_n(c))\ge0.
$$

所以不能将对角数组 $q_{n,n}$ 直接写成无缺陷的平均递推。右侧记录新阶段实际删除的条件质量；它不由改换指标自动消失。

由测度从上连续，固定 $n,c$ 时

$$
q_{n,s}(c)\downarrow q_n(c)
:=\mu(K\mid D_n(c)).
$$

有限求和允许取极限，得到最终平均递推

$$
q_n(c)=\frac13\sum_{j=0}^{2}q_{n+1}(c^{(j)}),
\qquad q_0(0)=M.
$$

还保留误差方向

$$
0\le q_{n,s}(c)-q_n(c)
=3^n\mu((K_s\setminus K)\cap D_n(c))
\le3^n(p_s-M).
$$

前缀上的这一递推可以作为动态规划使用；深度 $n$ 的原生状态集合有 $3^n$ 个元素，本式没有额外提供固定大小的状态压缩。

#### 2.10.3 支撑递推与概率递推的区别

令

$$
R_n=\{c:K\cap D_n(c)\ne\varnothing\},
\qquad r_n(c)=\mathbf 1_{R_n}(c).
$$

由每个正深度至多一个三进禁柱的祖先判据，一个柱如果没有被祖先或同深度禁类整个删去，其内部最多被真后代禁类删去相对质量 $1/2$。所以

$$
q_n(c)\in\{0\}\cup[1/2,1],
\qquad
c\in R_n\iff q_n(c)>0.
$$

这里把非空性与正质量等同，依赖该稀疏模型的已知间隔；一般有效闭集可以有非空零质量切片。

支撑满足另一条递推：

$$
r_n(c)=\max_{j=0,1,2}r_{n+1}(c^{(j)}).
$$

它只回答是否存在可延伸孩子。平均递推则计算三个实际孩子各自贡献的质量。对根节点已经有 $r_0(0)=1$，但 $q_0(0)=M<1$，所以不能用支撑指标替换条件概率。这里 $M<1$ 由至少一个停机程序产生的正质量禁柱保证。

有限阶段也可计算

$$
r_{n,s}(c)=\mathbf1_{\{K_s\cap D_n(c)\ne\varnothing\}},
$$

并且同一阶段满足 max 递推。对固定柱，$r_{n,s}(c)\downarrow r_n(c)$：若最终交为空，嵌套紧集 $K_s\cap D_n(c)$ 不可能一直非空，故某个有限阶段已空；若最终交非空，则每阶段都非空。这一逐点稳定性不给出统一可计算的稳定阶段。

在这个模型中，若整族最终 $q_n(c)$ 一致可计算，则质量间隔允许判定 $R_n$；进而逐次选一个可延伸孩子，就会产生 $K$ 的可计算点。因此最终 $q_n(c)$ 不可能作为整族一致可计算。不能由此断言每个单独数值都不可计算；某些值可以等于零。

#### 2.10.4 最终条件分布与 Doob 条件转移

定义概率律

$$
\nu_s(A)=\frac{\mu(A\cap K_s)}{p_s},
\qquad
\nu(A)=\frac{\mu(A\cap K)}{M}
$$

对所有 Borel 集 $A\subseteq X$。其前缀质量分别为

$$
\nu_s(D_n(c))=\frac{3^{-n}q_{n,s}(c)}{p_s},
\qquad
\nu(D_n(c))=\frac{3^{-n}q_n(c)}{M}.
$$

在 $q_n(c)>0$ 的父柱上，最终条件转移为

$$
P^K_n(c^{(j)}\mid c)
=\frac{\nu(D_{n+1}(c^{(j)}))}{\nu(D_n(c))}
=\frac{q_{n+1}(c^{(j)})}{3q_n(c)}.
$$

平均递推保证这三个非负数的和为 $1$。它是参考三叉均匀链的时变 Doob 条件变换：$q_n$ 是空间与深度共同索引的非负调和函数。

零质量父柱上的条件分布没有被 $\nu$ 决定。若要写成全域转移矩阵，可任取一个概率行补齐；从根按 $\nu$ 演化不会以正概率进入这些父柱，因而这种补齐不改变输出分布。

沿相容且正质量的前缀链 $c_0=0,c_1,\ldots,c_n$，连乘望远镜消去得到

$$
\prod_{i=0}^{n-1}P^K_i(c_{i+1}\mid c_i)
=\frac{q_n(c_n)}{3^nM}
=\nu(D_n(c_n)).
$$

这证明转移核恢复的是同一个最终条件概率律，不只是同一个非空支撑。

同样，对固定 $s$，将 $q_n,M$ 换成 $q_{n,s},p_s$ 就得到 $P^{K_s}$。这些有限阶段的核对有效父柱可精确计算；零父柱也能判定并补上任意概率行。每次改变 $s$ 会改变条件事件，不能把随深度切换不同 $s$ 的核直接认作 $P^K$。

#### 2.10.5 有限条件分布可计算，而且可实际采样

由于 $K_s$ 有有限柱描述，$\mu(K_s\cap D)$ 及 $p_s>0$ 均为可计算有理数。因此 $\nu_s$ 的所有柱集质量一致可计算；$s$ 也可以作为统一输入。

具体采样可先计算一个深度 $L_s$，使 $K_s$ 是若干深度 $L_s$ 柱的并。反复抽取均匀三进前缀，检查是否属于这些柱，首次接受后输出该前缀并继续输出独立均匀尾串，就得到 $\nu_s$。接受率为 $p_s$，故尝试次数的期望为

$$
\frac1{p_s}\le2.
$$

这是每个固定有限阶段的采样程序。它只控制尝试次数；每次检查所需的 $L_s$、计算有限描述的成本，以及取得指定最终误差需要选哪个 $s$，仍须分别计算。最终事件 $K$ 没有由此获得有限接受判据。

有限阶段采样落入最终集的概率为

$$
\nu_s(K)=\frac{M}{p_s}<1.
$$

它可以任意接近 $1$，却不在任何有限 $s$ 等于 $1$。对每个固定 $s$，这个成功概率本身不可计算，否则乘以已知 $p_s$ 就计算出 $M$。可计算概率律并不保证能计算任意有效闭事件的概率。

#### 2.10.6 总变差精确公式与不可计算收敛阶段

采用总变差距离约定

$$
d_{\mathrm{TV}}(\alpha,\beta)
=\sup_{A\text{ Borel}}|\alpha(A)-\beta(A)|
=\frac12\int\left|\frac{d\alpha}{d\mu}-\frac{d\beta}{d\mu}\right|d\mu
$$

其中最后的密度公式适用于本节相对于 $\mu$ 绝对连续的分布。由于

$$
\frac{d\nu_s}{d\mu}=\frac{\mathbf1_{K_s}}{p_s},
\qquad
\frac{d\nu}{d\mu}=\frac{\mathbf1_K}{M},
$$

且 $K\subseteq K_s$，分别在 $K$ 和 $K_s\setminus K$ 上积分，得到

$$
\begin{aligned}
d_{\mathrm{TV}}(\nu_s,\nu)
&=\frac12\left[
M\left(\frac1M-\frac1{p_s}\right)
+\frac{p_s-M}{p_s}\right]\\
&=1-\frac{M}{p_s}
=\frac{p_s-M}{p_s}.
\end{aligned}
$$

事件 $A=K$ 达到该上确界。因此 $p_s\downarrow M>0$ 给出

$$
\nu_s\longrightarrow\nu\quad\text{于总变差距离}.
$$

已知的 $1/2\le p_s\le1$ 保留双向误差控制

$$
p_s-M
\le d_{\mathrm{TV}}(\nu_s,\nu)
\le2(p_s-M).
$$

如果只使用下界 $M\ge1/2$，能得到可计算上界

$$
d_{\mathrm{TV}}(\nu_s,\nu)
\le1-\frac1{2p_s}.
$$

这个上界未必趋于零，不能替代总质量的任意精度信息。

不存在可计算函数 $g:\mathbb N\to\mathbb N$ 能保证

$$
d_{\mathrm{TV}}(\nu_{g(k)},\nu)\le2^{-k}
\quad\text{对每个 }k.
$$

否则

$$
0\le p_{g(k)}-M
=p_{g(k)}d_{\mathrm{TV}}(\nu_{g(k)},\nu)
\le2^{-k}
$$

会给出 $M$ 的可计算 Cauchy 名，矛盾。这已经排除了仅选一个精度合格阶段的可计算规则，当然也排除了保证所有后续阶段合格的可计算收敛模。

反过来，若在一个相同形式的模型中总质量可计算且有已知正下界，就可利用质量名及 $p_s\downarrow M$ 搜索足够小的 $p_s-M$，进而取得总变差收敛模。本例恰好缺少前一项，而不是缺少普通意义的收敛。

#### 2.10.7 没有可计算概率律能将全部质量放在 $K$

**命题 2.47。** 若 $\lambda$ 是三进数字空间上的可计算概率律，则

$$
\lambda(K)<1.
$$

证明之一直接使用 Bienvenu–Porter Lemma 3.5 的有限字母版本：若 $\lambda(K)=1$，这个正质量可计算，而 $K$ 有效闭，故 $K$ 含有可计算点，矛盾。

也可以只从支撑构造证明这一特例。对任意可计算概率律，根柱质量为 $1$。已选正质量父柱时，三个子柱至少有一个具有正质量；一致近似三个子柱的质量，等待某个严格正的有理下界，就可选择该孩子。逐层构造得到一个可计算点 $x$，其每个柱邻域均有正的 $\lambda$ 质量，因此 $x$ 属于 $\lambda$ 的拓扑支撑。

若 $\lambda(K)=1$ 且 $K$ 闭，支撑包含于 $K$：一个在 $K$ 外的点有与 $K$ 不交的柱邻域，该邻域质量为零。由此再次得到矛盾。这个支撑论证也说明，集中度为 $1$ 的此项不可能性只需目标集闭且没有可计算点；有效闭性是上面的文献引理所采用的更具体呈示。

特别地，最终条件分布 $\nu$ 不可计算，因为 $\nu(K)=1$。有限阶段 $\nu_s$ 却都可计算，且 $\nu_s(K)\to1$。因而

$$
\sup_{\lambda\text{ 为可计算概率律}}\lambda(K)=1,
\qquad
\lambda(K)<1\quad\text{对每个这样的 }\lambda.
$$

这个上确界没有可计算概率律达到。对指定族 $\nu_s$，C卷第2.10.6节还排除了依照任意精度有效选取合格阶段；本节没有把这一阶段不可能性扩张为对所有其他近似方案的复杂度结论。

对最终 Doob 核也有对应的统一性边界。假如存在一个可计算过程，能对每个正质量父柱一致给出正确的三个 $P^K$ 概率名，那么从根开始，每次选择一个已认证具有正转移概率的孩子，就会构造出 $K$ 的可计算点。即使该过程在零质量父柱上不作保证，沿上述构造也只查询其承诺域。故不存在这样的统一过程。这个结论不说每个单独转移概率都不可计算。

#### 2.10.8 几乎必然持续输出的可计算随机机器

下面的采样边界针对明确的机器模型。设随机输入带在给定的有限字母空间上服从可计算概率律 $\beta$，例如公平硬币，或参数可计算的有限字母 iid 源。在线机器的规则可计算，已经输出的数字不撤回，每个有限输出步骤只读取有限输入。假设它以 $\beta$ 概率 $1$ 最终输出无限三进串。

对有限输出字 $\sigma$，记 $O_\sigma$ 为“机器曾经输出以 $\sigma$ 开头的有限串”的输入事件。一次有限成功计算只读取有限随机带，因此 $O_\sigma$ 是一致有效开的事件，其概率

$$
z(\sigma)=\beta(O_\sigma)
$$

一致左可枚举。

固定输出长度 $n$，各 $O_\sigma$（$|\sigma|=n$）两两不交。几乎必然持续输出保证它们的并具有概率 $1$，于是

$$
z(\sigma)
=1-\sum_{\substack{|\tau|=n\\\tau\ne\sigma}}z(\tau).
$$

右侧同时给出一致右可枚举近似。因此 $z(\sigma)$ 一致可计算，并且是最终无限输出的柱集概率。整份输出概率律是可计算的。

这个证明不需要事先提供等待某个输出位的时间上界或收敛模。可计算上下近似及其保证相遇，足以对给定概率精度进行终止搜索；它没有宣称这一搜索很快。

成熟来源是 Bienvenu–Porter 同一固定版本 **第 5–6 页 Remark 2.2**：在公平二进制输入下，almost-total Turing functional 诱导可计算概率律；这里将同层有限输出分割的证明明确写出，并允许一般可计算输入概率律和三进输出。

结合C卷第2.10.7节，任何满足上述条件的机器都不可能以概率 $1$ 输出属于 $K$ 的无限串。结论仅排除全部概率集中到 $K$；公平三进 Haar 输出本身就是可计算随机过程，仍以概率 $M\ge1/2$ 落入 $K$。随机实现通常不可计算，和输出概率律可计算是不同性质。

若随机源参数不可计算、机器可使用非可计算 oracle，或没有几乎必然持续输出的条件，就不能直接套用此结论。闭性也不可省略：所有不可计算三进点组成的非闭集合具有 Haar 质量 $1$，所以“目标没有可计算点”本身不足以排除可计算随机源。

#### 2.10.9 允许停止时，半测度精确记录流失的质量

若机器有正概率只输出有限串，事件 $O_\sigma$ 的概率一般只满足

$$
z(\sigma)\ge\sum_{j=0}^{2}z(\sigma j).
$$

差额是输出到 $\sigma$ 后永不继续的概率。此时“曾经输出该前缀”的质量构成连续半测度，不能将其直接当成一份归一化的无限输出概率律。

真正无限输出部分的柱集质量为

$$
\overline z(\sigma)
=\lim_{m\to\infty}
\sum_{\substack{|\tau|=m\\\tau\succeq\sigma}}z(\tau).
$$

它是一份总质量至多为 $1$ 的次概率测度，总质量等于机器无限输出的概率。该极限和按无限输出事件重新归一化，都不自动保留可计算性。这是同一原始文献 **第 6 页 Theorem 2.3、第 7 页 Definition 2.4 与 Proposition 2.5** 的半测度及其 canonical measure 接口；本文使用三叉版本。

本例可以具体实现这一区别。用可计算 Haar 源生成 $x\in\mathbb Z_3$，在第 $n\ge1$ 阶段执行：

1. 读取足够多但有限的输入数字，检查 $x\in K_n$；
2. 若检查成功，输出 $x$ 的第 $n$ 个数字；
3. 若检查失败，永久停止输出。

$K_n$ 有统一可计算的 clopen 描述，故每次检查都在有限时间结束。由于近似嵌套，机器无限输出当且仅当 $x\in K$。在这一事件上，输出正是 $x$；否则只输出有限串。无限输出的概率是 $M<1$。

对长度 $n\ge1$、对应剩余类 $c$ 的前缀，半测度为

$$
z(c)=\mu(K_n\cap D_n(c))=3^{-n}q_{n,n}(c).
$$

约束更新的流失量精确等于

$$
z(c)-\sum_{j=0}^{2}z(c^{(j)})
=\mu((K_n\setminus K_{n+1})\cap D_n(c)).
$$

空前缀质量为 $1$；到第一层的流失量为 $1-p_1$。因而这种机器恰好实现C卷第2.10.2节在对角阶段出现的缺陷，而不是把缺陷隐去。

只保留永不停止部分，有

$$
\overline z(D_n(c))
=\lim_{m\to\infty}\mu(K_m\cap D_n(c))
=\mu(K\cap D_n(c)),
\qquad
\overline z(X)=M.
$$

其 canonical 次概率测度就是 $\mu(\,\cdot\cap K)$。再条件化于无限输出，才得到

$$
\frac{\overline z}{\overline z(X)}=\nu.
$$

因此，非可计算的最终条件分布可以作为这台可计算机器在非可计算成功事件上的条件律出现。机器不是以概率 $1$ 持续输出；无限成功也没有成为一个有限时间可宣布的认证。这与C卷第2.10.8节的排除结论完全相容。

#### 2.10.10 可复用的关系连接与边界

同一份约束在不同接口上给出四种严格不同的操作：

$$
\begin{array}{ll}
q_n=\frac13\sum q_{n+1}
&\text{运输同一概率律下的幸存质量},\\
r_n=\max r_{n+1}
&\text{运输是否存在相容延伸},\\
P^K=\dfrac{q_{n+1}}{3q_n}
&\text{在正质量父柱上条件化并生成联合律},\\
z_n-\sum z_{n+1}\ge0
&\text{记录约束更新或停止造成的流失}.
\end{array}
$$

有限阶段都有可计算描述，极限也作为闭集和概率律明确存在；但本例中不能有效取得最终延拓核、最终条件政策或任意精度的采样收敛阶段。有效提升、概率归一化和无限成功条件分别承担实质义务。

本节没有将收敛误差当成物理熵产生，没有将半测度流失当成某个物理守恒律，也没有将支持概率严格小于一表述为随机方法永远不能生成幸存点。这里认证的是固定数学模型中的表示、动态规划、条件化与计算接口。

## 3. 有限一致性与逻辑阈值

### 3.1 编码分辨率、有限一致性与自模拟铺砖：来源、条件及可用结论

本节依据有限一致性证明与自模拟铺砖的作者原文，给出编码运输与独立性迁移所需的明确条件。文献已经证明的结论、由其组织的普通数学推论，以及尚需对具体项目对象建立的桥梁，分别陈述。没有新增 Lean 声明或形式核验。

#### 3.1.1 Pudlák 的有限一致性定理确实包含可有效构造的多项式证明序列

主要依据为 Pavel Pudlák, *Reflection principles, propositional proof systems, and theories*, arXiv:2007.14835v1，2020 年 7 月 29 日；使用 PDF 自身页码。[EPAC PDF](https://iuuk.mff.cuni.cz/~koucky/EPAC/papers/TechRep-Pudlak-ArXiv-2007.14835.pdf) 与 [arXiv PDF](https://arxiv.org/pdf/2007.14835v1) 均提供这一固定版本。

第 23 页 §4.3 先定义 $\operatorname{Con}_T(x)$：不存在长度小于等于 $x$ 的 $T$ 中矛盾证明；$\bar n$ 为值等于 $n$、长度为 $O(\log n)$ 的闭算术项。因此 $\operatorname{Con}_T(\bar n)$ 的公式长度也是 $O(\log n)$。

同页 Theorem 4.8 的明确条件及结论是：若 $T$ 是有限公理化的 sequential theory，则存在多项式时间可计算的 $T$ 证明序列 $\{D_n\}$，其中 $D_n$ 证明 $\operatorname{Con}_T(\bar n)$，$n=1,2,\ldots$；并且在 $S^1_2$ 中可证明这些 $D_n$ 均为相应句子的 $T$ 证明。原文还紧接说明，1986、1987 年的构造给出相对于 $n$ 的多项式证明长度，其构造可在多项式时间内完成。第 24 页使用定理时再次明确写作 “in time polynomial in $n$”。

这里 sequential 是关于理论能够编码有限序列的专门性质，不是泛指“推理按步骤执行”。论文第 6 页 §2.3 的通篇工作背景是 $S^1_2$ 的有限扩张，采用标准 Hilbert 式一阶证明演算；使用其结果时，以满足此背景的有限公理化 sequential 理论为明确充分范围。不能从“有递归”或“可写程序”推出任意关系系统满足定理条件。

Theorem 4.8 的证明存在结论本身没有显式要求一致性；若还要声称这些有限一致性句子在标准自然数中为真，则须另外假定 $T$ 一致。不一致理论也可证明这些句子，这当然不使句子变真。

##### 3.1.1.1 长度参数不能由 $n$ 偷换为 $\log n$

此处 $n$ 是被排除的矛盾证明的长度上界，命题文本仅有 $O(\log n)$ 长。得到的是长度及构造时间 $n^{O(1)}$，不能宣称得到 $(\log n)^{O(1)}$。若把计算输入规定为普通二进制写出的 $n$，前者相对于输入位长可以是指数级；也可以使用一元输入 $1^n$，或相应长度参数，把“相对于 $n$ 多项式”表达成标准输入长度的多项式时间。

定理中的理论内句法正确性需要随所用数值表示和长度参数作恰当算术化。不能把作者对序列的简写直接强化为“存在一个以二进制 $n$ 为输入、在 $\operatorname{poly}(\log n)$ 时间内显式输出全部证明的程序”。后者与其明确的长度口径不同。

作者另一篇 [*Incompleteness in the finite domain*, arXiv:1601.01487v2](https://arxiv.org/pdf/1601.01487v2)，第 7–8 页 §2.5、§3.1 和 Theorem 3.1，提供有用的交叉定位：

- 第 4 页 Definition 1 的类 $\mathcal T$ 是一致的算术理论，扩张 $S^1_2$，公理集可在多项式时间判定。
- 第 7 页约定二进制数字项长 $O(\log n)$；未另指参数的多项式长度均指 $p(n)$。
- 第 8 页 Theorem 3.1 对该类理论给出某个 $\epsilon>0$ 的最短 $T$ 证明长度下界 $n^\epsilon$；当 $T$ 又有限公理化且 sequential 时，给出多项式于 $n$ 的上界。
- 第 8 页正文的线性上界使用 Rosser 的 C-rule 等具体证明演算条件；不能把这一改进无条件推广至任意证明格式。第 7 页也强调一般有向无环证明与纯树状证明的转换可能造成指数增长，不能忽略表示。

2020 年论文第 27 页列出的原始结果归属为：Pudlák, *On the length of proofs of finitistic consistency statements in first order theories*, **Logic Colloquium 84**，1986，165–196 页；以及 *Improved bounds to the length of proofs of finitistic consistency statements*, **Contemporary Mathematics 65**，1987，309–331 页。本节准确定理文本的直接来源是作者自己的 2020 年 Theorem 4.8 和 2017 年 Theorem 3.1；1986、1987 年文献只按上述作者综述中的归属列示，不作为逐字引文来源。

#### 3.1.2 有限实例、统一证明生成与一致性反思是不同断言

对具有标准可检验证明编码、足够算术表达能力且一致的 $T$，每个具体有限长度界可以逐一排除有限个矛盾证明候选，从而得到
$$
\forall n\in\mathbb N,\qquad T\vdash\operatorname{Con}_T(\bar n).
$$
Pudlák 的定理在规定的理论类中进一步改善其证明大小和生成方法。这个元层陈述与理论内断言
$$
T\vdash\forall x\,\operatorname{Con}_T(x)
$$
不同。普通一阶证明系统不含把无穷多已得实例一次提升为全称命题的无限 $\omega$-规则。

尤其不能把 Theorem 4.8 的“统一证明生成器可验证”删弱成“根本不可能存在统一生成器”。作者明确给出统一且可证明句法正确的生成。真正仍然缺失的是把“$D_n$ 是证明”转成所证句子的统一真值反思：
$$
\operatorname{Prf}_T(D_n,\ulcorner\operatorname{Con}_T(\bar n)\urcorner)
\quad\not\Longrightarrow\quad
\operatorname{Con}_T(\bar n)
$$
作为一个未经额外前提的理论内规则。关于标准自然数的外部逐项判断也不自动给出理论内部的全称证明。

这里缺的是对变量 $n$ 的统一反思。对每个固定的标准数 $n$，已有对应 $\operatorname{Con}_T(\bar n)$ 证明，故不能将这句读成每个固定实例的蕴含在 $T$ 中也不可证。

当 $T$ 还满足第二不完备定理的标准条件，且所用 $\operatorname{Con}_T$ 确实来自该标准可证谓词时，有
$$
T\nvdash\forall x\,\operatorname{Con}_T(x).
$$
这与有限实例的有效证明、乃至对生成器句法正确性的内部证明相容。2020 年第 23 页 Proposition 4.9 正是通过加入 $\operatorname{Con}_T$ 后可取得的反思，说明某种更强的统一证明序列认证会违反第二不完备定理；它没有否认 Theorem 4.8 的生成器。

#### 3.1.3 DRS 自模拟铺砖确有严格的层间恢复结构

依据 Bruno Durand, Andrei Romashchenko, Alexander Shen, [*Fixed-point tile sets and their applications*, arXiv:0910.2415v7](https://arxiv.org/pdf/0910.2415v7)，2014 年 12 月 4 日版本。以下页码均为 PDF 自身页码。

第 5 页 §2.1 定义 $\tau$ 以放大倍数 $N>1$ 模拟 $\rho$：每个 $\rho$ 瓦片映到一个 $N\times N$ 的 $\tau$ 宏块，并同时满足三个条件：映射单射；两瓦片匹配当且仅当对应宏块匹配；每个完整 $\tau$ 铺砖都能唯一分解为这些宏块。宏边颜色是边上 $N$ 个原颜色构成的序列。因此这里的“边界代表内部参与拼接”有具体注入性、匹配等价和唯一恢复条件，不能只凭图形相似称作同一定理。

第 6 页把“自相似”严格定义为瓦片集模拟自身。Proposition 1 证明其铺砖无非零周期：唯一宏块分解使任何周期向量被 $N$ 整除，缩放后重复此结论便要求它被所有 $N^j$ 整除。通过迭代模拟可构造任意大的有限铺砖，紧致性给出全平面铺砖。Theorem 2 断言这种自相似瓦片集存在。

第 8–9 页 §2.3 明确说其构造适配 Kleene 递归不动点定理的证明，不能仅直接调用定理结论。他们先构造模拟指定局部谓词的宏块，再使计算区中的程序核对高一层携带的程序位确为自身程序。所用 Kleene 不动点是程序语义等价意义的不动点，不要求程序文本或空间图像逐字符相同。

第 7 页已经把图灵机的时空计算表嵌入局部瓦片匹配规则。因此“铺砖规则中可承载计算”来自明确的局部计算模拟；不是从几何、自指或递归三个字直接推出通用性。

##### 3.1.3.1 可变放大率确能提供更长计算，但有资源条件

第 14–15 页 §5 使用序列 $\tau_0,\tau_1,\ldots$ 与 $N_0,N_1,\ldots$，其中 $\tau_j$ 以倍数 $N_j$ 模拟 $\tau_{j+1}$。多层宏块尺寸是累乘 $N_0\cdots N_{j-1}$。作者要求层号、父块坐标及放大率计算可放入当前计算区：例如层号与坐标所需的 $\log j+O(\log N_j)$ 位以及计算 $N_j$ 的运行时间，都须相对于可用的 $N_{j-1}$ 级别空间与时间足够小。任意递归选择的 $N_j$ 并不自动满足这些条件。

第 15 页作者明确说，可变放大结构不再满足此前固定放大率的严格 self-similar 定义，但仍可证明无周期；高层的计算区能执行更多步骤。应保留这一术语范围，不能把固定倍数不动点和所有可变层级直接写作同一个定义。

同页给出停机问题到 domino 问题的构造：在嵌入程序中并行运行指定机器 $M$ 的空带计算；若停机，就破坏铺砖。故其可计算构造的方向为
$$
M\text{ 不停机}\iff\tau(M)\text{ 有完整铺砖},
$$
或等价地
$$
M\text{ 停机}\iff\tau(M)\text{ 无完整铺砖}.
$$
因此 many-one 归约应写作 $\overline{\mathrm{HALT}}\le_m\mathrm{TILE}_{\mathrm{nonempty}}$，或 $\mathrm{HALT}\le_m\mathrm{TILE}_{\mathrm{empty}}$。笼统说“停机归约到 domino 问题”可以理解，但若写成“停机当且仅当存在铺砖”，便把这份构造的接受方向倒置。

这里的不可判定性针对输入随 $M$ 改变的一族有限瓦片集。它本身不证明任何另行指定的单个几何断言在 PA、ZFC 或其他固定理论中独立。

#### 3.1.4 有效编码保持可计算性及算术层级，须交代合法域

以下是普通数学的编码运输证明，不是 DRS 或 Pudlák 论文的额外结论。令 $\mathcal C\subseteq\Sigma^*$ 是可判定的合法代码集，有限字母词采用固定可计算自然数编码。设
$$
E:\mathbb N\longrightarrow\mathcal C
$$
为全可计算双射。因为 $\mathcal C$ 可判定，可定义整个词空间上的全可计算解码器 $\delta$：非法词返回零，合法词依次计算 $E(0),E(1),\ldots$ 直到匹配；双射保证合法输入的搜索终止。

对任意 $A\subseteq\mathbb N$，于是有
$$
E(A)=\{w\in\mathcal C:\delta(w)\in A\},\qquad
A=\{n:E(n)\in E(A)\}.
$$
全可计算原像保持可计算性；与可判定域取交也保持可计算性。因此 $A$ 可判定当且仅当作为全部有限词中子集的 $E(A)$ 可判定。

对通常算术层级的 $m\ge1$，全可计算原像保持 $\Sigma^0_m$ 和 $\Pi^0_m$，与可判定集合取交保持这两类，故
$$
A\in\Sigma^0_m\iff E(A)\in\Sigma^0_m,
\qquad
A\in\Pi^0_m\iff E(A)\in\Pi^0_m.
$$
这里层级按可计算关系上的数词量词交替定义。不能把这个结论未经说明地解释成“任意可计算换码都保持某固定算术语言中的有界量词公式 $\Delta_0$ 语法”。多项式时间复杂度也不从任意可计算双射得到保持；它需要双向复杂度和码长的相应界。

合法域条件承担实际作用。如果只有一个全可计算单射 $E$ 而其像 $\mathcal C$ 不可判定，那么取可判定集合 $A=\mathbb N$ 就有 $E(A)=\mathcal C$ 不可判定。例如任意无限可枚举、不可判定集合都可通过去重枚举成为某个全可计算单射的像。其逆在合法像上可部分计算，但这不提供对任意输入词的合法性判定。

所以“有效双射”必须说明是具有可判定合法域的有效表示，还是仅在合法输入承诺下可相互计算的表示。后一种承诺问题可以另行研究，但不能据此宣称 ambient 全词空间上的集合复杂度保持。

固定有限 $k\ge2$ 的规范 k-bonacci 有限整数代码具备所需合法性判定：检查有限词是否含 $1^k$、是否符合最高位非零的规范及零的单独约定，全部有限可判。整数编码与整数解码可有效执行。因此在这份明确的规范有限代码集上，上述双向保持结论适用；无限完成名字的可计算性及连续转换是另一问题，不由此结论解决。

#### 3.1.5 Gödel 条件不能缩成三个非形式关键词

本节以 [Stanford Encyclopedia of Philosophy, “Gödel’s Incompleteness Theorems”](https://plato.stanford.edu/entries/goedel-incompleteness/) 的 §2.5、§3.1–3.3 为条件来源；该来源是具名综述，Gödel 或 Rosser 原始论文全文不作为本节的直接引文依据。

一个明确且通用的第一不完备定理适用类是：一致、有效公理化、扩张 Robinson 算术 $Q$ 的经典一阶理论。有效公理化需使证明可有效枚举，并使用相应的标准可验证证明编码。满足条件时，可构造依赖于该理论的不可判定句。

必须区分两种构造：对于普通 Gödel 句 $G_T$，一致性足以得到 $T\nvdash G_T$；要同时按这一构造保证 $T\nvdash\neg G_T$，标准条件可取 $\Sigma^0_1$ 健全性，即 1-consistency，原始表述使用更强的 $\omega$-一致性。Rosser 的改进另构造句子 $R_T$，对有效公理化且扩张 $Q$ 的一致理论，普通一致性已经足以保证 $R_T$ 两侧都不可证。不能把 Rosser 的较弱前提自动套回未经修改的普通 Gödel 句。

第二不完备定理还依赖一致性句的具体算术化。一个足够的标准设置是：$T$ 一致且具有所需算术强度，标准可证谓词 $\operatorname{Prov}_T$ 满足 Hilbert–Bernays–Löb 型可导性条件，包括可证明性的内化、modus ponens 的内化及正内省。此时 $T$ 不能证明由该可证谓词定义的自身一致性。

仅说一个谓词在标准自然数中与“可证明”同外延，不保证第二定理适用。SEP §3.1–3.3 特别以 Rosser 可证谓词说明：随意更改一致性表达式会改变理论内可证明性。实际迁移中应指定标准可证谓词并核对可导性条件，或直接使用一个已知满足条件的理论及其现成定理。

“有效通用性＋自编码＋对角不动点”可作为找构造的纲领；它不是替代这些条件的充要定理。一个有限自动机可以递归运行，一个结构可以自相似，一个完成空间可以有无限线程，而这些事实均不单独保证它具有 Gödel 不完备性所需的算术表达和有效证明体系。

#### 3.1.6 家族不可判定性不能自动变成固定 E7 的独立性

要证明一族几何任务算法不可判定，一条充分路线是有效地把已知不可判定问题归约进该族，并证明归约对所有合法输入双向保持目标真值。DRS 给出的是这种有具体模拟与资源控制的路线。

但“必须先证明整个 odd-distinct geometry 通用计算，才能证明某固定 E7 独立”不是必要性定理。固定命题独立性是相对于某个明确理论 $T$ 的两条元命题：$T\nvdash E7$ 和 $T\nvdash\neg E7$。它可以由具体解释、保守性结果、模型构造或与已知独立句的理论内等价得到，不要求先把整个几何类提升为通用计算系统。

例如，若对某个满足 Rosser 条件的 $T$，已经证明 $T\vdash E7\leftrightarrow R_T$，则一致性下两侧独立性直接运输。这只是说明需要怎样的桥梁，并未证明实际 E7 有该等价。若只证明 $T\vdash E7\to\operatorname{Con}_T$，第二不完备定理只给 $T\nvdash E7$；不能据此宣称反面也不可证。甚至 $E7\leftrightarrow\operatorname{Con}_T$ 配合单纯一致性，也不能无条件推出 $T\nvdash\neg E7$，因为一致性并不等于 $\Sigma^0_1$ 健全性。

反过来，即使某整个任务族已有 HALT 归约，族中大量固定实例仍可直接证明或反驳；族的不可判定性不会替一个指定实例选择它在特定理论中的逻辑状态。要从通用族中取得特定独立实例，仍须选定与 $T$ 关联的程序或句子，并在足够明确的基础理论内证明实例对应。

本节不提供实际 E7、odd-distinct 几何、某个指定 Kleene tree 或 resolution 结构之间的新归约。相关桥梁仍需逐一满足共同合法域、有效映射、方向正确的真值对应、资源条件及必要的理论内可形式化性。

#### 3.1.7 可直接保留的统一命题及其边界

对这里讨论的有效体系，一个可成立的共同结构是：有限局部证书可以逐层生成并验证，整体的相容实现、有效选择、统一算法与理论内反思则是不同的额外任务。Pudlák 的结果说明“所有有限实例均有高效证明”与“不能内部证明全称一致性”能够同时成立；DRS 的构造说明局部关系确实能被设计成层间自模拟并承载任意长计算；有效有限整数换码保留算术层级则要求可判定合法域。

上述三者建立了可具体使用的对应，但没有证明“每次分辨率增加必然遇到新的独立命题”，也没有把有限前缀的信息不足、无可计算路径、HALT 不可判定及固定理论的句子独立四种障碍认作同一个定理。把它们联系起来的每条箭头，都须由其对应的归约、构造或理论内证明承担。

## 追加锚（本行以下为增补区）
## 4. 幸存质量、条件概率与真实延拓的可组合接口

### 4.1 有效外部体积与加权最大密度

**定义 4.1.1（共同对象及外部体积）。** 固定概率空间 $(X,\mathcal B,\mu)$，其中 $\mu(X)=1$，及可测集 $K$，记
$$
0<M=\mu(K)\le1,\qquad \nu(E)=\frac{\mu(E\cap K)}M\quad(E\in\mathcal B).
$$
每个 $n$ 给出一个有限可测分割 $\mathcal D_n=\{C_{n,i}:i\in I_n\}$，所有实际参考权重 $w_{n,i}=\mu(C_{n,i})$ 严格为正，但同层不必相等。定义
$$
R_n=\{i\in I_n:K\cap C_{n,i}\ne\varnothing\},\qquad
A_n=\bigcup_{i\in R_n}C_{n,i},\qquad a_n=\mu(A_n).
$$
这里 $R_n$ 包含非空但质量为零的切片；它不是某个有限计算阶段的候选集，也不是正条件概率单元的同义词。以下外部体积条件是一项独立供应：
$$
0\le a_n-M\le\varepsilon_n,\qquad \varepsilon_n\longrightarrow0.
$$
有效版本还给出层选择器 $N$，使 $\varepsilon_{N(k)}\le2^{-k}$。它只选择一个合格层；不要求 $N$ 单调，也不自带所有后续层都合格的模量。基本估计不要求各分割嵌套。

**命题 4.1.2（密度夹逼）。** 令
$$
D_n=\max_{i\in I_n}\frac{\nu(C_{n,i})}{w_{n,i}},\qquad m_n=D_n^{-1}.
$$
则
$$
1\le D_n\le M^{-1},\qquad
M\le m_n\le a_n\le M+\varepsilon_n.
$$

**证明。** 对每个单元，$\mu(K\cap C_{n,i})\le w_{n,i}$，所以密度比至多为 $1/M$。按参考质量加权，全部密度比的平均是
$$
\sum_{i\in I_n}w_{n,i}\frac{\nu(C_{n,i})}{w_{n,i}}
=\sum_{i\in I_n}\nu(C_{n,i})=1,
\qquad \sum_{i\in I_n}w_{n,i}=1.
$$
故最大值至少为一。不可延拓单元的条件概率为零，因此
$$
1=\sum_{i\in R_n}\nu(C_{n,i})
\le D_n\sum_{i\in R_n}w_{n,i}=D_na_n.
$$
取倒数即得结论。$R_n$ 内的零质量单元只在右侧增加参考体积，不影响这个不等式。证明没有把非空性换成正质量。证毕。

**命题 4.1.3（细化的单调性及其限度）。** 若 $\mathcal D_{n+1}$ 细化 $\mathcal D_n$，则 $D_n\le D_{n+1}$，因而 $m_{n+1}\le m_n$。配合定义 4.1.1 的外部体积条件，$m_n\downarrow M$。

**证明。** 设粗单元 $C$ 由细单元 $C_j$ 分割。其密度比为
$$
\frac{\nu(C)}{\mu(C)}
=\sum_{C_j\subseteq C}\frac{\mu(C_j)}{\mu(C)}
  \frac{\nu(C_j)}{\mu(C_j)}.
$$
各系数非负且和为一，所以不超过细层最大值。对粗层取最大值得到第一式；倒数与夹逼给其余结论。证毕。

嵌套及定性收敛本身不提供有效外部体积误差。命题 4.4.5 将给出嵌套的标准前缀分割、可计算条件律及不可计算总质量，说明这里不能省去有效误差供应。

**定理 4.1.4（非均匀实权重的质量算法）。** 假设 $I_n$ 的完整有限列表统一可计算，$w_{n,i}>0$ 和 $\nu(C_{n,i})$ 的实数名对 $(n,i)$ 统一可计算，且供应定义 4.1.1 的有效层选择器。则可统一计算 $M$，无需延拓查询或预给 $M$ 的正下界。

**证明及精度。** 正实数的名字可用于搜索一个正有理下界：若 $|v(t)-w|\le2^{-t}$，等待 $v(t)-2^{-t}>0$，再取其一半。对有限层逐个执行，所有搜索都终止。设已得 $0<\ell<w$，对 $y=\nu(C)\in[0,1]$ 和 $w$ 作误差至多 $\alpha<\ell/2$ 的有理近似 $\widetilde y,\widetilde w$，则 $\widetilde w>\ell/2$，且
$$
\left|\frac{\widetilde y}{\widetilde w}-\frac y w\right|
\le\frac{2\alpha}{\ell}+\frac{2\alpha}{\ell^2}.
$$
因此可有效选择 $\alpha$，将每个密度比计算到任意要求的绝对精度；有限最大值不放大共同误差。

对要求 $2^{-k}$ 的质量精度，取 $n=N(k+2)$，计算有理 $d_n$，使 $|d_n-D_n|\le2^{-k-2}$，并令 $\widetilde D_n=\max(1,d_n)$。因 $D_n\ge1$，截断不增加误差。倒数在 $[1,\infty)$ 上满足
$$
\left|\frac1x-\frac1y\right|=\frac{|x-y|}{xy}\le|x-y|.
$$
于是输出 $1/\widetilde D_n$ 的误差满足
$$
\left|\frac1{\widetilde D_n}-M\right|
\le2^{-k-2}+\varepsilon_{N(k+2)}
\le2^{-k-1}<2^{-k}.
$$
实际算法只遍历完整分割并计算实际权重及条件概率。$A_n,R_n$ 只用于正确性证明，没有隐藏的非空性查询。证毕。

### 4.2 总质量、条件律、总变差阶段与精确在线采样

**定义 4.2.1（有效乘积模型及五个接口）。** 从本节起，取
$$
X=\prod_{j\ge1}\Sigma_j,
$$
其中每个非空有限字母表 $\Sigma_j$ 都有统一可计算的完整有序列表。合法有限词及每层完整列表可有效取得，$[\sigma]$ 表示标准前缀柱。clopen 集以有限标准柱并表示；细化到共同深度后，空性、交、并、补都可有限计算。参考概率 $\mu$ 的全部标准柱质量统一可计算，不要求数字独立或质量有理。

给定同一条统一可计算的递减 clopen 序列 $K_s$，令
$$
K=\bigcap_{s\ge0}K_s,\qquad p_s=\mu(K_s)\downarrow M>0,
\qquad \nu_s(E)=\frac{\mu(E\cap K_s)}{p_s},\qquad
\nu(E)=\frac{\mu(E\cap K)}M.
$$
计算阶段 $s$ 与前缀深度 $n$ 分别索引。由有限 clopen 运算，$p_s$ 和 $\mu(K_s\cap[\sigma])$ 是统一可计算实数，一般不必有理。若阶段来自禁柱枚举，以有限计算时间截断；没有新公告也必须结束该阶段。

相对于同一个 oracle $A$，规定以下输入输出接口：

- $\mathbf M$ 是有理 Cauchy 名 $v_M(t)$，满足 $|v_M(t)-M|\le2^{-t}$。
- $\mathbf R$ 是全部合法有限词的真实延拓特征函数，$R(\sigma)=1$ 当且仅当 $K\cap[\sigma]\ne\varnothing$；非法词返回零。
- $\mathbf C$ 对每个 $(\sigma,t)$ 给出误差至多 $2^{-t}$ 的 $\nu([\sigma])$ 有理近似；空词概率为一。
- $\mathbf T$ 是全函数 $g$，对所指定的同一阶段序列满足 $d_{\mathrm{TV}}(\nu_{g(k)},\nu)\le2^{-k}$。定义只要求一个合格阶段，不预设 $g$ 单调。
- $\mathbf S$ 是以公平 iid 随机位为输入、可使用 $A$ 的在线机器。每次有限输出只读有限输入，已输出字母不撤回，以概率一持续产生无限合法串，且无限输出的 Borel 分布恰为 $\nu$。

这些是承诺域上的机器或名字转换，不要求转换器先判定输入的正质量、有效误差或几乎必然持续输出承诺。几乎必然不表示对每条随机带都成功；$\mathbf S$ 不供应逐位等待模量。名字也可以包含无关额外信息，故“某个实数为 $A$-可计算”不等于“它的每个名字恰有某一 Turing 度”。若呈示或参考律本身使用 oracle，这份访问必须计入共同输入。

调用第 4.1 节时，还须给每个分割单元的有效 clopen 描述、完整有限列表、严格正实际权重，以及有效外部体积误差。$\mathbf C$ 可通过不交标准柱分解计算单元概率。这些分割不必生成整个拓扑：一旦恢复质量，可借同一 $K_s,\mu$ 恢复完整标准柱律。只有抽象单元标签而没有它们与标准柱的有效集合关系，不足以完成这一步，也不足以产生实际数字流。

**命题 4.2.2（总变差与质量的精确对应）。** 采用 $d_{\mathrm{TV}}(\alpha,\beta)=\sup_{E\text{ Borel}}|\alpha(E)-\beta(E)|$ 的约定，有
$$
d_{\mathrm{TV}}(\nu_s,\nu)
=\frac12\int\left|\frac{\mathbf1_{K_s}}{p_s}-\frac{\mathbf1_K}M\right|\,d\mu
=\frac{p_s-M}{p_s}.
$$
该距离随 $s$ 非增并趋于零，上确界在 $E=K$ 达到。

**证明。** 这是第 2.10.6 节的同一指示密度计算：将那里的三进空间、Haar 律及下界 $1/2$ 分别换成本节 $X,\mu$ 与唯一需要的 $M>0$。密度在 $K$ 上的差积分为 $M(1/M-1/p_s)$，在 $K_s\setminus K$ 上为 $(p_s-M)/p_s$，其余为零；两项相等，半和给所示式。$\nu(K)=1$、$\nu_s(K)=M/p_s$ 说明该事件达到上确界。函数 $p\mapsto1-M/p$ 在 $p>0$ 上递增，故 $p_s\downarrow M$ 给单调性与收敛。本计算不使用稀疏性、等权分割或已知数值正下界。证毕。

**定理 4.2.3（质量与总变差阶段的有效互算）。** 在定义 4.2.1 的模型上，$\mathbf M\leftrightarrow\mathbf T\longrightarrow\mathbf C$ 均匀成立。

**证明及算法。** 先由质量名搜索有理 $0<\ell<M$。对 $\eta=2^{-k}$，取得有理 $L<M$ 且 $M-L<\eta\ell/2$；例如选择足够高精度后取名字近似减去两倍误差。并行搜索各阶段的严格不等式
$$
p_s-L<\eta\ell.
$$
可计算实数的严格比较可半判定；必须交错提高各阶段的比较精度，不能固定在一个不合格的早期 $s$ 永远等待。因 $p_s\downarrow M$，某阶段有严格裕度，搜索终止。该阶段满足
$$
d_{\mathrm{TV}}(\nu_s,\nu)=\frac{p_s-M}{p_s}
<\frac{p_s-L}{\ell}<\eta.
$$
对每个 $k$ 独立得到一个选择值后，取前 $k+1$ 个值的最大值，便得非递减选择器；由命题 4.2.2 的单调性，它还保证此后所有阶段合格。

反向给任意选择器 $g$，无论它是否单调，都有
$$
0\le p_{g(k)}-M=p_{g(k)}d_{\mathrm{TV}}(\nu_{g(k)},\nu)\le2^{-k},
$$
这里使用了 $p_s\le1$。若阶段质量为精确有理数，直接输出 $p_{g(k)}$。一般实阶段下，为请求误差 $2^{-j}$，先取 $s=g(j+1)$，再将 $p_s$ 近似至误差至多 $2^{-j-1}$，两项误差之和至多 $2^{-j}$。

对条件柱同样有 $|\nu_{g(k)}([\sigma])-\nu([\sigma])|\le2^{-k}$。为请求 $2^{-j}$，使用 $s=g(j+1)$，把 $\nu_s([\sigma])$ 计算到误差至多 $2^{-j-1}$。每个 $p_s>0$，从其实数名搜索正有理下界后执行除法，即可完成此数值计算。此处也没有要求阶段质量有理。证毕。

若再给定义 4.1.1 的有效外部体积条件，第 4.1 节提供 $\mathbf C\to\mathbf M$，四个概率接口中的质量、条件律与总变差选择遂可互算。只有这条反向箭头消耗外部体积误差；一般归一化并不自动保留可恢复的归一化常数。

**定理 4.2.4（公平源的精确区间采样）。** $\mathbf C$ 均匀计算 $\mathbf S$，包括相对于任意同一 oracle 的版本。

**证明。** 公平位 $(\xi_i)_{i\ge1}$ 给出均匀随机数 $U=\sum_{i\ge1}\xi_i2^{-i}\in[0,1]$。根区间为 $[0,1]$。按字母表顺序，把每个前缀 $\sigma$ 的区间按子柱概率 $\nu([\sigma a])$ 切成相邻子区间，使长度为 $\nu([\sigma a])$。父子概率的有限可加性保证恰好填满父区间；等价地，每层用全部词的字典序累积概率取端点。两种定义相容，全部端点都是由有限和给出的可计算实数。

读取有限公平位得到包含 $U$ 的二进有理区间，同时提高端点精度。只有当已严格认证 $U$ 位于某一子区间的内部时，才输出该子字母。对于已选前缀，继续同一细分；不重新抽取 $U$，也不撤回已有输出。认证用的是严格不等式，不需要测试端点是否相等。

所有有限层的端点构成可数集，均匀 $U$ 落在其中的概率为零。在其补集上，每一层存在唯一包含 $U$ 的区间内部；正距离保证有限精度即能认证。因此每个输出位都在有限时间出现，同时全部位持续输出的事件仍有概率一。前缀 $\sigma$ 被输出的事件除零测端点外就是其长度为 $\nu([\sigma])$ 的区间，所以输出律的全部柱概率正确，进而 Borel 律为 $\nu$。

零质量柱只占空区间，永远不会被严格内部测试选中。整个算法不做零父柱除法，不需要判定哪些柱质量为零。证毕。

**定理 4.2.5（持续输出计算其概率律）。** $\mathbf S$ 均匀计算 $\mathbf C$，无需输出等待模量。

**证明。** 使用第 2.10.8 节的输出事件证明，作如下有限字母及 oracle 适配。对合法词 $\sigma$，令 $O_\sigma$ 为机器曾输出该前缀的公平随机带事件。每次成功发生都有有限计算和有限输入见证；枚举所有这样的见证并去重计算有限柱并，得到相对于 $A$ 的有效开集及递增有理概率下近似 $l_{\sigma,s}\uparrow\Pr(O_\sigma)$。在一个固定深度 $n$，只有有限多个词，输出不可撤回使这些事件两两不交，几乎必然无限生产使它们的并有概率一。因此
$$
\Pr(O_\sigma)=1-\sum_{\substack{|\tau|=n\\\tau\ne\sigma}}\Pr(O_\tau).
$$
其他事件的下近似给本事件的上近似。搜索上下差小于要求精度的时刻必终止；输出事件概率就是最终无限输出的柱概率。每层可以有不同字母表，所用性质只是该层完整列表有限且有效。证毕。

由此，在一般有效乘积正质量模型中已有 $\mathbf M\leftrightarrow\mathbf T\to\mathbf C\leftrightarrow\mathbf S$；加入有效外部体积供应后，四项均匀等价。两个采样转换均未给一般期望运行时间。公平源确实是构造的输入，不能无条件换成任意可计算源；例如确定性源不能产生非退化随机律。

第 2.10.9 节的停止流例仍承担必要的边界：允许正概率有限停止时，曾输出前缀的质量仅满足 $z(\sigma)\ge\sum_a z(\sigma a)$，无限输出部分为
$$
\overline z(\sigma)=\lim_{m\to\infty}
\sum_{\substack{|\tau|=m\\\tau\succeq\sigma}}z(\tau).
$$
该节逐阶段检查同一个三进 $K_n$ 的机器，其 canonical 次概率正是 $\mu(\,\cdot\cap K)$，总质量为 $M$；在无限成功事件上重新归一化才得到 $\nu$。其完整流失公式和构造保持在原节。此机器不满足 $\mathbf S$ 的概率一持续输出合同；正概率成功不能代替它。单个随机实现不可计算，与整份输出律可计算，也是不同性质。

### 4.3 真实延拓、局部质量定位与概率支撑

**命题 4.3.1（延拓计算外部体积）。** 在第 4.1 节的有效 clopen 分割和有效外部体积条件下，$\mathbf R$ 均匀计算 $\mathbf M$，从而计算四个概率接口。

**证明。** 将每个 $C_{n,i}$ 表为有限标准柱并。它与 $K$ 非空相交，当且仅当其中至少一个标准柱延拓查询为真，因此有限 OR 给出 $R_n$。计算实际加权和
$$
a_n=\sum_{i\in R_n}w_{n,i}.
$$
为请求 $2^{-k}$，取 $n=N(k+1)$，将该有限实数和近似到误差至多 $2^{-k-1}$，再用 $0\le a_n-M\le2^{-k-1}$ 即得。不得把实际权重换成单元数量除以层大小。证毕。

**命题 4.3.2（数量化局部间隔）。** 假设对每个标准柱 $C$ 统一供应可计算实数 $c_C>0$，保证
$$
K\cap C\ne\varnothing\quad\Longrightarrow\quad\mu(K\cap C)\ge c_C.
$$
则 $\mathbf C$ 均匀判定 $\mathbf R$，不需要 $M$ 的数值正下界。

**证明。** 因 $\mu(X)=1$，有 $M\le1$，所以非空时
$$
\nu(C)=\frac{\mu(K\cap C)}M\ge\mu(K\cap C)\ge c_C.
$$
空时该概率为零。搜索正有理 $r_C<c_C$，把 $\nu(C)$ 近似到误差严格小于 $r_C/4$，以阈值 $r_C/2$ 比较。空时近似小于 $r_C/4$，非空时大于 $3r_C/4$；两侧与阈值分离，故决定正确。证毕。

**命题 4.3.3（独立的支撑路线）。** 在定义 4.2.1 的有效闭呈示下，若另有承诺
$$
K=\operatorname{supp}\nu,
$$
则 $\mathbf C$ 也能均匀判定 $\mathbf R$，无需预给数量化局部间隔。

**证明。** 对标准柱 $C$ 并行做两项搜索：以其概率名半判定 $\nu(C)>0$；逐阶段检查有效 clopen 集 $K_s\cap C$ 是否为空。若 $K\cap C$ 非空，其中的点属于支撑，且 $C$ 为开邻域，故 $\nu(C)>0$，第一项终止。若最终交为空，递减紧集 $K_s\cap C$ 不可能全部非空：否则有限交性质及紧致性给出最终交中的点。因此某有限阶段交已经为空，第二项终止。两项互斥，因为第二项成功意味着 $\nu(C)=0$，而第一项成功意味着最终交非空。故程序总终止并决定延拓。有限个柱的并可用同样论证，或使用有限 OR。证毕。

支撑承诺给出的是每个非空开邻域的正质量，不是每个无限点的正单点质量。Pauly–Fouché 的支撑正信息结果只承担 $C\cap\operatorname{supp}\nu\ne\varnothing\iff\nu(C)>0$ 这一正半判定；这里的负分支依赖所给有效闭呈示和紧致 clopen 查询，已单独证明。此路线没有给出统一概率精度或运行时间界。若存在非空零质量切片，两项搜索在该柱上都可能不终止；正总质量本身排除不了这一情况。

**引理 4.3.4（同一总质量的局部化区间）。** 允许 $M=0$，不定义归一化律也可以进行以下计算。对同一可计算参考概率、递减 clopen $K_s\downarrow K$ 及总质量名，固定 clopen 查询 $C$，令
$$
m_C=\mu(K\cap C),\qquad f_s=\mu(K_s),\qquad
u_s^{\mathrm{raw}}=\mu(K_s\cap C),\qquad \ell_t=v_M(t)-2^{-t}.
$$
为使本引理的标量不与概率律 $\nu_s$ 混淆，下文简记 $u_s=u_s^{\mathrm{raw}}$。则
$$
\max\{0,\ell_t-(f_s-u_s)\}\le m_C\le u_s,
\qquad
0\le u_s-\max\{0,\ell_t-(f_s-u_s)\}\le f_s-\ell_t.
$$

**证明。** 第 2.3.3 节已拥有有限分割的质量局部化；第 2.7.2 节式（TM.570）—（TM.571）给它的单柱形式。此处以二元可测分割 $C,X\setminus C$ 接入同一论证：$f_s-u_s=\mu(K_s\setminus C)\ge\mu(K\setminus C)$，且 $\ell_t\le M$，故左端不超过 $M-\mu(K\setminus C)=m_C$。右端来自集合包含。若最大值取第二项，宽度等于 $f_s-\ell_t$；若取零，则 $\ell_t\le f_s-u_s$，仍有 $u_s\le f_s-\ell_t$。因此不要求阶段质量恰为有理，亦不要求 $M>0$。证毕。

**定理 4.3.5（一般实阶段的一次质量查询决策）。** 设已供应有理 $g>0$，并承诺该查询满足：空切片质量为零，非空切片有 $m_C>g$。给定同一呈示、参考律及总质量名，可只查询一次质量名，决定该切片是否非空。

**证明及完整误差分配。** 选 $t$ 使 $2^{-t}\le g/16$，读取 $v_M(t)$，固定 $\ell_t=v_M(t)-2^{-t}$，则
$$
0\le M-\ell_t\le2^{1-t}\le g/8.
$$
逐个有限阶段计算 $f_s$ 的有理近似，误差严格小于 $g/48$，再加 $g/48$，得到有理上界
$$
f_s\le F_s<f_s+g/24.
$$
每阶段只需有限精度计算，随后用有理比较检查
$$
F_s-\ell_t<g/3.
$$
不满足就进入下一阶段。由于
$$
F_s-\ell_t<f_s-M+g/24+g/8=f_s-M+g/6,
$$
且 $f_s\downarrow M$，该搜索必终止。此时引理 4.3.4 给 $0\le u_s-m_C<g/3$。再取有理 $u$，使 $|u-u_s|<g/12$。空时 $u<g/3+g/12=5g/12$；非空时 $u>m_C-g/12>11g/12$。故
$$
K\cap C\ne\varnothing\quad\Longleftrightarrow\quad u>g/2.
$$
等号不会出现。这个证明允许一般可计算实阶段，严格实数比较已被具有误差保证的有理比较替代。给定请求指数只控制这一次质量访问的精度，不控制公告等待、有限并整理或参考测度计算的时间。证毕。

若目标只是近似 $m_C$，可把引理 4.3.4 的区间宽度与数值近似误差分别压到所需精度，再输出区间中的有理近似；这仍适用于零总质量。把该质量近似进一步转成非空判断，才需要定理 4.3.5 的局部间隔，或命题 4.3.3 的独立支撑承诺。

**命题 4.3.6（真实外逼近的尾包含）。** 在标准前缀乘积空间中，令 $K=X\setminus\bigcup_{w\in\mathcal P}[w]$，不先要求稀疏性。以真实延拓定义 $A_n=\bigcup_{|\sigma|=n,\,R(\sigma)=1}[\sigma]$。则
$$
K\subseteq A_n,\qquad
A_n\setminus K\subseteq\bigcup_{\substack{w\in\mathcal P\\|w|>n}}[w].
$$
若每个正深度至多一个最终禁柱，且深度 $h$ 的柱质量至多 $u_h$，进一步有
$$
0\le\mu(A_n)-M\le\sum_{h>n}u_h.
$$

**证明。** 第一包含直接来自真实延拓的定义。对 $x\in A_n\setminus K$，令 $D$ 为其深度 $n$ 柱，选取同柱幸存者 $y\in D\cap K$。存在一个禁柱 $[w]$ 包含 $x$；若 $|w|\le n$，前缀嵌套使 $D\subseteq[w]$，从而 $y$ 也被删除，矛盾。故其深度大于 $n$。对这一包含作可数次可加性的上界，再用每深度预算即得尾估计。证毕。

这里只用了“真实延拓必无禁祖先”的必要方向。若将真实延拓替换为某个语法祖先测试，还须另证充分方向；一般情况下不能如此替换。原禁柱可以嵌套或冗余，尾和只是并集上界，不是原始公告清单的精确删除质量。可有效趋零的尾和才履行第 4.1 节的外部体积条件。

### 4.4 均匀变量进制、点态恢复与两种非稀疏反例

**定义 4.4.1（球对称稀疏合同及既有几何）。** 采用第 2.9.1 节的模型：可计算整数 $b_n\ge2$，
$$
B_0=1,\qquad B_n=\prod_{j=1}^n b_j,\qquad w_n=B_n^{-1},\qquad
X=\prod_{n\ge1}\{0,\ldots,b_n-1\},
$$
参考律为逐坐标均匀乘积律。深度 $n$ 的全部 $B_n$ 个柱都具有质量 $w_n$。一份固定 c.e. 公告呈示在每个正深度至多有一个最终禁柱，允许重复同一公告，不允许根柱及同深度竞争。令 $K$ 为禁柱并的补集；本节讨论归一化概率接口时要求 $M>0$。零质量时 $\nu$ 未定义，第 2.8.4 节及第 2.9 节关于集合延拓的结论仍按各自条件成立。

第 2.9.2 节的紧致有限子覆盖证明已给出最终祖先判据、规范最小禁柱确实出现在原呈示中的事实，以及规范深度支撑 $S_{\mathrm{depth}}$ 的精确信息：
$$
1-M=\sum_{h\in S_{\mathrm{depth}}}w_h,\qquad R\equiv_T S_{\mathrm{depth}}.
$$
这里 $S_{\mathrm{depth}}$ 与采样接口 $\mathbf S$ 不同。该质量等式只对两两不交的规范基成立，不能改成含冗余项的原清单之和。由命题 4.3.6 及同一权重尾和，真实外逼近满足
$$
0\le a_n-M\le t_n:=\sum_{h>n}w_h\le w_n\le2^{-n}.
$$
局部间隔则由第 2.9.3 节的另一恒等式供应：
$$
\delta_d=w_d-t_d=\sum_{j>d}(b_j-2)w_j.
$$
非空深度 $d$ 切片的原始质量至少为 $\delta_d$。其严格正性等价于存在某个 $j>d$ 使 $b_j>2$；紧邻的 $j=d+1$ 也计入。找到这样的 $j$ 就得到正有理下界 $(b_j-2)w_j\le\delta_d$。全局尾误差与局部正间隔负责不同方向，不能互换。

**定理 4.4.2（保留层查询成本的等权算法）。** 定义
$$
v_n=\max_{|\sigma|=n}\nu([\sigma]),\qquad m_n=\frac{w_n}{v_n}.
$$
则
$$
v_n\ge w_n>0,\qquad M\le m_n\le a_n\le M+t_n\le M+w_n.
$$
从 $\mathbf C$ 请求误差 $2^{-k}$ 的 $M$ 近似时，可取 $n=k+2$，查询全部 $B_n$ 个柱，每个查询的绝对误差至多
$$
\eta=w_n2^{-k-2}.
$$
若接口仅接受二进精度指数，选择 $t$ 满足 $2^{-t}\le\eta$ 即可。

**证明及算法。** 全层概率之和为一，故 $v_n\ge1/B_n=w_n$；最大值必须取整个完整层，不需要先找 $R_n$。将命题 4.1.2 中所有 $w_{n,i}$ 取为 $w_n$，有 $D_n=v_n/w_n$，立即得到夹逼；其证明允许 $R_n$ 内有零质量切片。

设全部查询近似的最大值为 $z_n$，令 $\widetilde v_n=\max(w_n,z_n)$。有限最大值及截断均不增加误差，所以 $|\widetilde v_n-v_n|\le\eta$。由两者至少为 $w_n$，
$$
\left|\frac{w_n}{\widetilde v_n}-\frac{w_n}{v_n}\right|
=\frac{w_n|\widetilde v_n-v_n|}{\widetilde v_nv_n}
\le\frac\eta{w_n}=2^{-k-2}.
$$
再加 $a_n-M\le w_n\le2^{-k-2}$，总误差至多 $2^{-k-1}<2^{-k}$。这给具体的 $B_{k+2}$ 次条件概率查询，适用于全二进及最终二进情形，均不先恢复延拓。证毕。

**定理 4.4.3（五接口的量词）。** 对定义 4.4.1 的全部可计算进制序列与正质量呈示，$\mathbf M,\mathbf C,\mathbf T,\mathbf S$ 均匀互算，$\mathbf R\to\mathbf M$ 亦均匀成立。若另承诺非二进层无限多，则五项均匀互算。对每个固定可计算进制序列及固定可计算呈示，五项的 $A$-可计算性对任意 oracle $A$ 点态等价，即使进制最终全为二也如此。

**证明。** 尾界和定理 4.4.2 接入第 4.2 节，给四项概率接口；反向延拓查询逐层求 $a_n=|R_n|w_n$，给质量。无限非二进承诺下，在深度 $d$ 搜索后续 $b_j>2$，得到有理 $g_d=(b_j-2)w_j>0$。因 $M\le1$，非空柱有 $\nu([\sigma])\ge\delta_d\ge g_d$；将概率算到误差小于 $g_d/4$、以 $g_d/2$ 作阈值即可。或者用第 2.9.6 节的质量定位算法。根处也有 $\delta_0>0$，所以此承诺自动保证总质量正。

点态结论使用第 2.9.4–2.9.5 节的精确权重展开定理。唯一数值展开时，由质量名可统一提取 $S_{\mathrm{depth}}$，再用同一呈示恢复 $R$；若展开有歧义，第一处分歧之后必须全部为二进，其两支恰为终止尾与全一尾。实际支撑因而有限或余有限，存在把实际有限资料写为常量的程序。这个存在论证足以给每个固定对象的相对可计算性，却没有提供从呈示及任意质量名统一选出正确常量的程序，也不先判定是否最终二进或找出最后例外深度。结合四概率接口的统一转换，即得所述点态等价。证毕。

无限非二进时，每个与 $K$ 相交的柱都有正条件概率，因而 $K=\operatorname{supp}\nu$；闭性给另一包含。最终二进时可以保留概率看不见的零质量分支。正质量点的选取、整个条件律的采样、全部延拓的判定各是不同接口。进制计算、完整层大小、概率精度、公告等待和采样读取成本均须分别计算；无界进制可使 $B_n$ 远大于要求的精度规模。

**命题 4.4.4（最终二进尾上的四输入相同家族）。** 固定某个 $d\ge0$，使 $b_n=2$ 对所有 $n>d$ 成立，并固定深度 $d$ 柱 $[c]$；$d=0$ 时取根。存在一族统一可计算的稀疏呈示，其 $\mathbf M,\mathbf C,\mathbf T,\mathbf S$ 可以分别使用完全相同的名字或机器，但从各自呈示索引及这些四个共同输入不能统一恢复 $\mathbf R$。

**证明。** 对机器编号 $e$，无条件公告 $[c0^n1]$，$n\ge1$；若机器停机，再公告 $[c0]$。它们的深度分别为 $d+n+1$ 和 $d+1$，满足每正深度预算。固定公告覆盖 $[c0]\setminus\{c0^\infty\}$，故
$$
K_e=
\begin{cases}
X\setminus[c0],&e\text{ 停机},\\
(X\setminus[c0])\cup\{c0^\infty\},&e\text{ 不停机}.
\end{cases}
$$
单点的质量至多 $w_d2^{-n}$ 对所有 $n$ 成立，因而为零。全部质量同为
$$
M_e=1-w_d/2\ge1/2,
$$
全部 Borel 条件律也同为 $\mu(\,\cdot\mid X\setminus[c0])$。因此可以供给同一个有理质量名和同一条件柱概率程序。使用公平位精确生成各有限均匀数字，反复取深度 $d+1$ 的前缀，拒绝落在 $[c0]$ 的前缀；接受后输出它并继续独立均匀尾。每次只测试这 $d+1$ 位，接受率为 $M_e$，期望尝试次数 $1/M_e\le2$。有限均匀字母可用公平二进整数拒绝采样实现，故这也确是一台共同的公平位机器；尝试次数界不等于位成本或总运行时间界。

规定第 $s$ 阶段已公告前 $s$ 个固定禁词，并模拟原机器 $s$ 步，$s=0$ 时尚未公告固定禁词。未发现停机时，额外保留的柱是 $[c0^{s+1}]$，所以
$$
p_{e,s}-M_e=w_d2^{-s-1},\qquad
 d_{\mathrm{TV}}(\nu_{e,s},\nu_e)
\le w_d2^{-s}\le2^{-s}.
$$
发现停机后误差为零。故所有呈示共用 $g(k)=k$。此阶段是所定义的有限调度，不等于实现该调度所用的机器指令数。

但 $R_e(c0)=1$ 当且仅当机器 $e$ 不停机。若有统一转换器，供给这四个相同输入和可由 $e$ 构造的呈示，即能判定不停机，矛盾。每个固定 $R_e$ 仍可判：两种集合形式分别给有限 clopen 判定，或再加“是否为 $c0^\infty$ 的前缀”的判定。这不违反点态等价。

特别取 $b_1=3$、$b_n=2$（$n\ge2$），$d=1,c=0$。第 2.9.7 节已算得 $\delta_0=1/3$、$\delta_1=0$，本家族的 $M_e=5/6$，查询为 $[00]$。全局质量非二进有理、根处有正间隔，都不能修复深层零分支。证毕。

这一家族与定理 4.4.3 一起说明：对固定可计算进制序列，跨全部正质量稀疏呈示统一恢复五接口，当且仅当非二进层无限多。此数学分类不提供判定任意进制程序是否满足无限非二进条件的算法。反例使用固定有限 $d$，没有要求从任意最终二进程序找出它。

**命题 4.4.5（独立非零块：可计算条件律与不可计算质量）。** 在公平二进空间中，存在一个固定正质量有效闭集，其 $\mathbf C,\mathbf S,\mathbf R$ 均可计算，而 $\mathbf M$ 不可计算，任何给定有效递减 clopen 呈示都没有可计算的总变差选择器。

**证明。** 取无限 c.e. 不可判定集 $H\subseteq\mathbb N_0$，以无重复的可计算序列 $e_1,e_2,\ldots$ 枚举它。无限性保证取得每个下一项的搜索终止。把原始位按连续块分割，第 $j$ 块长
$$
\ell_j=2(e_j+1),\qquad q_e=4^{-e-1}.
$$
令 $K$ 要求每块都不是全零。每个有限块边界可计算，违反某块的事件是有效 clopen，故 $K$ 有效闭。块独立及测度从上连续给
$$
M=\prod_{e\in H}(1-q_e).
$$
对每个有限子积，用 $\prod_i(1-q_i)\ge1-\sum_iq_i$，再取极限，得
$$
M\ge1-\sum_{e\ge0}4^{-e-1}=\frac23.
$$

假设 $M$ 可计算。归纳判定 $e$ 是否属于 $H$：已知所有 $i<e$ 的答案后，可计算正有理积 $P_{<e}=\prod_{i<e,\,i\in H}(1-q_i)$，并计算实数 $P_e=M/P_{<e}$。若 $e\in H$，则 $P_e\le1-q_e$；若 $e\notin H$，则
$$
P_e=\prod_{i>e,\,i\in H}(1-q_i)
\ge1-\sum_{i>e}q_i=1-q_e/3.
$$
两区间间隙为 $2q_e/3$。例如近似至误差小于 $q_e/6$，与 $1-2q_e/3$ 比较即能判定本项。由 $e=0$ 起归纳得到 $H$ 的判定程序，矛盾。因此 $M$ 不可计算。

另一方面，对一个有限前缀，计算足够多的 $e_j$，直至找到覆盖它的块边界。已完成块若有全零块便不可延拓；否则尚未完成的块总能在剩余位置填一位 $1$，以后每块也取一个非零串。这给全部延拓的判定，不需要判定某个任意整数是否属于 $H$。

条件律可直接计算。若前缀完成前 $j$ 块，并指定下一块长为 $t<\ell_{j+1}$ 的部分串 $a$，且前面完整块全为非零，则
$$
\nu([\sigma])
=\left(\prod_{i=1}^j\frac1{2^{\ell_i}-1}\right)
\frac{2^{\ell_{j+1}-t}-\mathbf1_{\{a=0^t\}}}{2^{\ell_{j+1}}-1}.
$$
$t=0$ 时后一因子为一；若某完整块全零，概率为零。证明是在原始分子中，完整指定块贡献 $2^{-\ell_i}$，部分块贡献合法完成数乘 $2^{-\ell_{j+1}}$，之后独立块贡献其存活概率积；除以 $M$ 后，尾积精确消去。所有消去合法，因为 $M\ge2/3>0$。故最终条件律是各块独立、均匀分布于非零串的乘积律，公式为可计算有理数。逐块用公平位抽取均匀二进块并拒绝全零串，即给精确采样器；每块有限等待几乎必然终止，可数交仍给无限生产概率一。

若存在总变差选择器，定理 4.2.3 就计算出 $M$，矛盾。这一对象同时反驳一般的 $\mathbf C\to\mathbf M$、$\mathbf R\to\mathbf M$ 和 $\mathbf S\to\mathbf T$。它不满足稀疏预算：删除后续块全零，须在许多旧前缀下同时删除同一原始深度的柱；即使只列此前已通过的块前缀，第二块起仍有多个。故没有违反定理 4.4.3。证毕。

**命题 4.4.6（不可判零质量分支）。** 在公平二进空间中，存在另一个固定有效闭集，其 $\mathbf M,\mathbf C,\mathbf T,\mathbf S$ 均可计算，而 $\mathbf R$ 不可判定。

**证明。** 固定 c.e. 不可判定集 $H\subseteq\mathbb N_0$，令
$$
C_e=[1^{e+1}0],\qquad z_e=1^{e+1}0^\infty,\qquad
K=[0]\cup\{1^\infty\}\cup\{z_e:e\notin H\}.
$$
各 $C_e$ 两两不交，$z_e$ 在 $e\to\infty$ 时只趋于 $1^\infty$，该点已经包含；与闭的 $[0]$ 合并后，$K$ 闭。更具体地，其补集可有效枚举：对所有 $e$，枚举 $C_e\setminus\{z_e\}$，这由尾部首次出现 $1$ 的有限柱给出；若 $e$ 进入 $H$，再枚举整个 $C_e$。每个以 $1$ 开始且不等于 $1^\infty$ 的串属于唯一 $C_e$，因此这份枚举精确给出补集。

除 $[0]$ 外只有可数多个点，公平测度均为零，所以 $M=1/2$，且对全部 Borel 事件 $\nu=\mu(\,\cdot\mid[0])$。共同条件律可计算，先输出零再输出公平尾就是精确采样器；总变差选择器由质量名和上述同一有效呈示经定理 4.2.3 得到。但是
$$
K\cap C_e\ne\varnothing\quad\Longleftrightarrow\quad e\notin H,
$$
所以延拓不可判定。这是一个固定呈示的点态失败，不只是命题 4.4.4 那种跨呈示选择程序的失败。其非空 $C_e$ 切片也只有零质量点，明确显示支撑承诺缺失。证毕。

### 4.5 有限观察精度、弱拓扑与总变差精度

**定义 4.5.1（观察距离）。** 对定义 4.2.1 的紧有限字母乘积，令 $Q_n$ 读取前 $n$ 个字母。对 Borel 概率 $\alpha,\beta$，定义
$$
T_n(\alpha,\beta)
=d_{\mathrm{TV}}((Q_n)_*\alpha,(Q_n)_*\beta)
=\frac12\sum_{|\sigma|=n}|\alpha([\sigma])-\beta([\sigma])|,
\qquad
d_{\mathrm{obs}}(\alpha,\beta)=\sum_{n\ge1}2^{-n}T_n(\alpha,\beta).
$$
和式绝对收敛，因为 $0\le T_n\le1$。这里 $T_n$ 是有限层距离，$\mathbf T$ 是阶段选择接口，两者不同。

**命题 4.5.2（有限层和整体距离的界）。** 对 $N\ge1$，
$$
T_n\le T_{n+1}\le d_{\mathrm{TV}}(\alpha,\beta),\qquad
d_{\mathrm{obs}}\le d_{\mathrm{TV}}(\alpha,\beta),
$$
$$
2^{-N}T_N\le d_{\mathrm{obs}}
\le(1-2^{-N})T_N+2^{-N},\qquad T_N\le2^N d_{\mathrm{obs}}.
$$

**证明。** 对任意可测推前 $f$，推前中的事件差就是原空间中 $f^{-1}(E)$ 的事件差，所以总变差不增加。$Q_n$ 是 $Q_{n+1}$ 的进一步推前，给第一组界。以权重 $2^{-n}$ 求和得到 $d_{\mathrm{obs}}\le d_{\mathrm{TV}}$。和式保留第 $N$ 项给下界；前 $N$ 项各不超过 $T_N$，权重和为 $1-2^{-N}$，余项不超过 $\sum_{n>N}2^{-n}=2^{-N}$，给上界。最后一式由下界重排。证毕。

**定理 4.5.3（度量与弱拓扑）。** $d_{\mathrm{obs}}$ 是概率测度空间上的度量，且诱导紧乘积空间上的弱收敛拓扑。

**证明。** 非负性、对称性与三角不等式逐项成立，并由非负求和保留。若距离为零，每个 $T_n=0$，因而全部柱概率相同；标准柱连同空集组成生成 Borel 集的 $\pi$ 系统，概率测度唯一性定理给 $\alpha=\beta$。故不仅是伪度量。

若 $\alpha_j$ 弱收敛至 $\alpha$，每个 clopen 柱的指示函数连续，因此固定层的有限多个柱概率都收敛，$T_N(\alpha_j,\alpha)\to0$。先选 $N$ 压小 $2^{-N}$，再用命题 4.5.2 控制其余有限和，得观察距离趋零。

反向，观察距离趋零给每个固定层 $T_N\to0$。紧乘积上的连续实函数 $f$ 一致连续；因此对任意 $\epsilon>0$，存在 $N$，使同一深度 $N$ 柱内 $f$ 的振幅小于 $\epsilon$。每柱选一个代表值，得到前缀阶梯函数 $f_N$，满足 $\|f-f_N\|_\infty<\epsilon$。其积分是有限柱概率的线性组合，故 $\int f_N\,d\alpha_j\to\int f_N\,d\alpha$。两端近似误差之和小于 $2\epsilon$，令 $\epsilon\downarrow0$ 即得弱收敛。复连续函数分别处理实虚部。证毕。

**命题 4.5.4（小观察误差不能控制全部 Borel 事件）。** 在二进空间中，令 $x=0^\infty$、$x_N=0^N10^\infty$，则
$$
d_{\mathrm{TV}}(\delta_{x_N},\delta_x)=1,\qquad
d_{\mathrm{obs}}(\delta_{x_N},\delta_x)=2^{-N}.
$$

**证明。** 单点事件 $\{x_N\}$ 的概率差为一，故总变差为一。前 $n\le N$ 位相同，$T_n=0$；对 $n\ge N+1$，两个前缀不同，$T_n=1$。求和得 $\sum_{n>N}2^{-n}=2^{-N}$。证毕。

这个例子说明弱拓扑严格弱于总变差拓扑，不否定命题 4.2.2 中指定条件阶段序列本身的总变差收敛。

**定理 4.5.5（条件柱名与有效观察阶段）。** 更一般地，给定一列概率律 $(\nu_s)$，其标准柱概率对 $(s,\sigma,t)$ 统一可计算，并承诺每个有限边缘收敛到 $\nu$ 的相应边缘。令 $\mathbf W$ 是相对于同一 oracle 的全函数 $h$，满足
$$
d_{\mathrm{obs}}(\nu_{h(k)},\nu)\le2^{-k}.
$$
则 $\mathbf C\leftrightarrow\mathbf W$ 均匀成立，无需稀疏性、总质量或外部体积界。

**证明及精度。** 给 $\mathbf C$，为计算 $h(k)$，取 $N=k+2$、$\eta=2^{-k-2}$。固定层只有有限多个柱，$T_N(\nu_s,\nu)$ 是可计算实数。依次考察 $s=0,1,\ldots$，每次仅计算到固定精度，取得有理数
$$
T_N(\nu_s,\nu)\le U_s<T_N(\nu_s,\nu)+\eta/2.
$$
例如先以误差小于 $\eta/4$ 近似 $T_N$，再加 $\eta/4$。若 $U_s<\eta$ 就接受，否则进入下一阶段，不在早期不合格阶段等待严格比较终止。有限边缘收敛保证足够后的 $T_N<\eta/2$，因而搜索终止。被接受阶段有
$$
d_{\mathrm{obs}}(\nu_s,\nu)\le T_N+2^{-N}
<2^{-k-1}<2^{-k}.
$$

反向，对于深度 $N\ge1$ 的柱和精度 $2^{-m}$，取 $s=h(N+m+2)$。命题 4.5.2 给
$$
|\nu_s([\sigma])-\nu([\sigma])|
\le T_N(\nu_s,\nu)
\le2^N d_{\mathrm{obs}}(\nu_s,\nu)\le2^{-m-2}.
$$
把阶段柱概率再近似到误差至多 $2^{-m-2}$，总误差至多 $2^{-m-1}<2^{-m}$。空词直接输出一。证毕。

这个 $h$ 只选一个合格阶段，不自动给所有后续阶段的模量。即使 $K_s$ 递减，归一化后的有限边缘距离或观察距离也未由上述论证取得单调性；总变差的特殊单调公式不能移作它们的证明。若深度 $N$ 的层大小记为 $B_N=\prod_{j=1}^N|\Sigma_j|$，正向每个尝试阶段遍历 $B_{k+2}$ 个柱；例如把每个阶段及最终柱概率的误差取小于 $\eta/(8B_N)$，则半差和误差小于 $\eta/4$，足以形成上述上界。反向的观察精度请求为 $N+m+2$。这些是查询与精度成本，没有给尝试阶段数或总运行时间界。

**命题 4.5.6（同一个非零块对象的有效观察与无效总变差）。** 对命题 4.4.5 的同一 $H$、同一块和同一 $K$，取完整块阶段
$$
K_j^{\mathrm{blk}}=\{x:\text{前 }j\text{ 块全非零}\},\qquad
\nu_j^{\mathrm{blk}}=\mu(\,\cdot\mid K_j^{\mathrm{blk}}),\qquad
L_j=\sum_{i=1}^j\ell_i,\quad L_0=0.
$$
令 $J_N=\min\{j:L_j\ge N\}$。则对所有 $j\ge J_N$，深度 $N$ 的边缘已经与最终 $\nu$ 精确相同；因而 $h(k)=J_{k+1}$ 是可计算观察选择器，且本例在该阶段之后也都合格。然而没有可计算总变差选择器。

**证明。** 取得每个 $e_j$ 的搜索终止，且块长至少为二，所以 $L_j\to\infty$，$J_N$ 可计算。深度 $N$ 的前缀事件只涉及前 $J_N$ 块。对 $j\ge J_N$，以后各块与该事件及这些块独立；分子与分母中的额外块存活因子完全消去，所得公式就是命题 4.4.5 的最终前缀公式。故前 $N$ 层距离全为零，$d_{\mathrm{obs}}(\nu_j^{\mathrm{blk}},\nu)\le2^{-N}$。取 $N=k+1$ 给所称选择器及其特殊的所有后续阶段保证。

完整块阶段也是统一可计算的递减 clopen 呈示，质量趋于同一个不可计算 $M$。若它有总变差选择器，定理 4.2.3 将计算该 $M$，矛盾。命题 4.2.2 仍给普通意义的总变差收敛。证毕。

这里的 $j$ 是已完成块数，不是 c.e. 枚举的机器步数。计算 $J_N$ 可能等待尚未枚举出的块标签；无限性保证终止，没有给跨所有此类枚举的统一时间界。在第 4.4 节的稀疏合同中，$\mathbf W$ 可加入四概率接口，但 $\mathbf W\to\mathbf T$ 的有效转换经过 $\mathbf C\to\mathbf M$ 及有效外部体积，而非两种距离之间一个一般的有效反向比较。最终二进尾的延拓障碍依旧存在。

### 4.6 Rényi 倾斜、平方倾斜与充分局部间隔

**定义 4.6.1（同一 iid 律及按词长计费的库存）。** 固定已知有限字母表 $A$，$|A|\ge2$，及严格正、归一化概率向量 $p=(p_a)_{a\in A}$。在 $Y=A^{\mathbb N_0}$ 上取同一 iid 律 $\mu_p$，记
$$
p(w)=\mu_p([w])=\prod_{i<|w|}p_{w_i},\qquad p(\varnothing)=1.
$$
最终禁词族 $\mathcal P$ 在每个正词长至多一个词，不含空词；可有限或无限，可重复报告同一词。设
$$
U=\bigcup_{w\in\mathcal P}[w],\qquad E=Y\setminus U.
$$
算法额外使用完整 c.e. 呈示和统一可计算的 $p_a$ 实数名，严格正性及归一化为承诺。对查询 $v$，“无禁祖先”指最终不存在 $w\in\mathcal P$ 满足 $w\preceq v$，包含 $w=v$ 的情形；有限阶段尚未看到祖先不构成这一承诺的证书。

对实数 $q>1$，用自然对数定义
$$
c_q=\sum_{a\in A}p_a^q,\qquad
r_q=c_q^{1/(q-1)},\qquad
H_q(p)=\frac{\log c_q}{1-q}=-\log r_q.
$$
由于至少两个 $p_a$ 严格为正且和为一，每个 $p_a<1$，故 $0<c_q<\sum_a p_a=1$，进而 $0<r_q<1$。

**定理 4.6.2（倾斜前缀族的 Hölder 界）。** 若有限或可数词族 $\mathcal F$ 无前缀冲突、不含空词、每个正长度至多一词，则
$$
\sum_{w\in\mathcal F}p(w)\le
B_q:=\left(\frac{r_q}{1-r_q}\right)^{(q-1)/q}.
$$
这个估计对全部 $q>1$ 成立；它是否小于一是另一个条件。

**证明。** 定义辅助概率
$$
\widehat p_a=\frac{p_a^q}{c_q},\qquad
\widehat p(w)=\prod_{i<|w|}\widehat p_{w_i}
=\frac{p(w)^q}{c_q^{|w|}}.
$$
各项正且和为一，所以确实给出一个辅助 iid 概率律。前缀自由使这些辅助柱两两不交，故对每个有限子族有总质量至多一；取非负和的极限得
$$
\sum_{w\in\mathcal F}\widehat p(w)\le1.
$$
在可数索引集 $\mathcal F$ 上，取
$$
f(w)=\widehat p(w),\quad g(w)=r_q^{|w|},\quad
\alpha=1/q,\quad\beta=(q-1)/q.
$$
$f,g$ 非负，$\alpha,\beta>0$ 且 $\alpha+\beta=1$。上式证明 $f$ 可和；长度映射在 $\mathcal F$ 上单射且值为正整数，故
$$
\sum_{w\in\mathcal F}g(w)\le\sum_{n\ge1}r_q^n=\frac{r_q}{1-r_q}<\infty,
$$
证明了第二个可和性前提。逐项又有
$$
f(w)^\alpha g(w)^\beta
=\widehat p(w)^{1/q}c_q^{|w|/q}=p(w).
$$
因此可应用非负可和实函数的可数加权 Hölder 不等式，得到
$$
\sum_w p(w)
\le\left(\sum_w f(w)\right)^{1/q}
   \left(\sum_w g(w)\right)^{(q-1)/q}
\le B_q.
$$
对应的仓内通用声明是 `CountableWeightedHolderInterpolation.countable_weighted_holder_interpolation`；上面逐项履行了它的非负性、两项可和性和互补正指数条件。等价地，可先对每个有限子族使用指数 $q,q/(q-1)$ 的 Hölder，再取非负和极限。辅助柱的加法性是在实际倾斜概率中证明的，不是有限均匀二元 Kraft 公式的无条件替换。证毕。

**推论 4.6.3（平方倾斜的完整代入）。** 令 $c=\sum_a p_a^2$。上述结论在 $q=2$ 时为
$$
\widehat p_a=\frac{p_a^2}{c},\qquad
\widehat p(w)=\frac{p(w)^2}{c^{|w|}},\qquad
\sum_{w\in\mathcal F}p(w)\le\sqrt{\frac c{1-c}}.
$$

**证明。** 此时 $r_2=c$，逐词关系为 $p(w)=\sqrt{\widehat p(w)}c^{|w|/2}$。对有限子族直接作 Cauchy–Schwarz：
$$
\sum_w\sqrt{\widehat p(w)}c^{|w|/2}
\le\left(\sum_w\widehat p(w)\right)^{1/2}
    \left(\sum_w c^{|w|}\right)^{1/2}
\le\sqrt{\frac c{1-c}}.
$$
第一和由辅助柱不交控制，第二和由不同正长度及几何级数控制。可数版由有限子集的非负和极限得到，正是定理 4.6.2 的同一专门化。证毕。

**定理 4.6.4（有限压缩与共同尾律的局部余量）。** 若 $r_q<1/2$，记
$$
\eta_q=1-B_q>0.
$$
则 $\mu_p(E)\ge\eta_q$；对任何无最终禁祖先的词 $v$，
$$
\mu_p(E\cap[v])\ge\eta_q p(v)>0.
$$
有禁祖先时切片为空。特别地，真实延拓等价于无最终禁祖先，且 $E=\operatorname{supp}(\mu_p(\,\cdot\cap E)/\mu_p(E))$。平方情形 $c<1/2$ 给 $\eta_2=1-\sqrt{c/(1-c)}$。

**证明。** 对每个有限公告集，先去掉重复词，再去掉具有更短已公告祖先的词。保留族前缀自由、无空词，柱并不变，每正长度至多一词的预算也保留。由定理 4.6.2，每个有限公告并的质量至多 $B_q$。有限公告并递增至 $U$，测度从下连续给 $\mu_p(U)\le B_q$，故根处余量成立。这里不枚举最终规范基；有限阶段的可计算压缩已经足够。

若 $v$ 无最终禁祖先，每个与 $[v]$ 相交的禁柱都是真后代，唯一写成 $[vu]$，其中 $|u|\ge1$。删去共同前缀后，绝对深度 $|v|+n$ 的至多一词变成每相对正深度 $n$ 至多一词。因同一个参考律是 iid，在 $[v]$ 内条件化后的尾仍为 $p$。对每个有限尾库存作前述压缩，再取递增极限，局部相对删除量至多 $B_q$；乘以 $p(v)>0$ 得所示下界。若有禁祖先，整个 $[v]$ 已删除。对根取空词，因禁止根公告，没有祖先，故根也在本论证范围内。

每个非空柱切片均有正条件概率，故 $E$ 中每点属于支撑；闭的 $E$ 承载全部条件概率，故支撑包含于 $E$。证毕。

数值条件 $H_q(p)>\log2$、$r_q<1/2$、$B_q<1$ 等价。这仅比较所给上界，不是“每个具体幸存集具有正质量”的必要充分条件。倾斜概率只用于估计，最终质量和采样仍相对于原来的 $\mu_p$。

**定理 4.6.5（Shannon 严格条件及有效证书搜索）。** 令
$$
H(p)=-\sum_a p_a\log p_a.
$$
若严格承诺 $H(p)>\log2$，并供应可计算严格正概率向量，则能有效找到有理 $q>1$、$0<\rho<1/2$ 和 $\gamma>0$，满足
$$
r_q<\rho,\qquad
0<\gamma<1-\left(\frac\rho{1-\rho}\right)^{(q-1)/q}<\eta_q.
$$
给同一禁词呈示及总质量名后，可统一恢复全部真实延拓。

**证明。** 有限性和 $p_a>0$ 允许逐项微分：
$$
p_a^{1+\epsilon}=p_a+\epsilon p_a\log p_a+o(\epsilon),
\qquad
c_{1+\epsilon}=1-\epsilon H(p)+o(\epsilon).
$$
利用 $\log(1+x)=x+o(x)$，
$$
\log c_{1+\epsilon}=-\epsilon H(p)+o(\epsilon),\qquad
H_{1+\epsilon}=-\frac{\log c_{1+\epsilon}}\epsilon\longrightarrow H(p).
$$
所以在严格熵承诺下，所有充分靠近一的 $q>1$ 都有 $H_q>\log2$，特别序列 $q_j=1+1/j$ 中存在合格项。

算法先从每个 $p_a$ 的名字搜索正有理下界；这些下界及有限实数运算允许统一计算对数、幂、$c_{q_j}$ 和 $r_{q_j}$。第 $m$ 轮对所有 $1\le j\le m$ 各求一个宽度至多 $2^{-m}$ 的包含区间。只要某个上端 $u<1/2$ 就接受该 $j$。每轮有限，固定的合格 $j$ 在充分精度后必成功；不能选一个可能不合格的 $j$ 永远等待。取
$$
q=q_j,\qquad \rho=(u+1/2)/2.
$$
于是 $r_q\le u<\rho<1/2$。实数 $\zeta=1-(\rho/(1-\rho))^{(q-1)/q}$ 可计算且严格正；搜索正有理下界再取其一半为 $\gamma$。由于 $r\mapsto(r/(1-r))^{(q-1)/q}$ 严增，便得所需严格链。

再搜索每个字母的正有理 $0<\ell_a<p_a$，对查询词 $v$ 定义
$$
g_v=\gamma\prod_{i<|v|}\ell_{v_i}>0,
$$
空积为一。定理 4.6.4 给非空切片的质量至少 $\eta_qp(v)>g_v$，空切片为零。因此使用定理 4.3.5，选择一般的 $t$ 满足 $2^{-t}\le g_v/16$，便从一次总质量查询及同一呈示决定本词延拓。这里不能把特定 Perron 模型的 $t=L(v)+7$ 直接代入任意 $g_v$。证毕。

搜索无需预给熵差的正数值下界，也没有判定严格熵承诺的真伪；在承诺外不保证终止。证书搜索时间、$q-1$、$\gamma$、各 $\ell_a$、局部精度与禁词公告等待分别影响成本，不能从该充分条件推出统一快速算法。

**命题 4.6.6（严格扩展平方准则的有理实例）。** 概率向量
$$
p=(7/10,3/20,3/20)
$$
不满足平方正余量条件，但满足定理 4.6.4 的 $q=3/2$ 条件；对全部满足其词长预算的库存，有 $\mu_p(E)>1/200$，无禁祖先柱的局部条件幸存比例也大于 $1/200$。

**证明。** 三项正且和为一，直接计算
$$
c_2=\frac{107}{200}>\frac12,
\qquad
c_{3/2}=\frac{7\sqrt{70}+3\sqrt{15}}{100},
\qquad
r_{3/2}=c_{3/2}^2=\frac{3565+210\sqrt{42}}{10000}.
$$
因 $42<169/4$，$\sqrt{42}<13/2$，故
$$
r_{3/2}<\frac{493}{1000}<\frac12.
$$
此时 $(q-1)/q=1/3$，所以
$$
\eta_{3/2}
>1-\left(\frac{493}{507}\right)^{1/3}>\frac1{200}.
$$
最后一个严格号由精确有理证书
$$
\left(\frac{199}{200}\right)^3-\frac{493}{507}
=\frac{51463693}{4056000000}>0
$$
及立方函数的严格单调性得到。定理 4.6.4 给全局与局部结论。平方条件失败只说明该特定估计未给正余量，没有推出实际零质量；这里另一个倾斜指数确实扩大了充分条件的适用范围。证毕。

**命题 4.6.7（任意阶的熵比较）。** 对定义 4.6.1 的任意 $q>1$，$H_q(p)\le H(p)$。

**证明。** 在有限分布 $p$ 下，对随机变量 $Z(a)=(q-1)\log p_a$ 使用指数函数的 Jensen 不等式，再取对数，得
$$
\log c_q=\log\mathbb E_p e^{(q-1)\log p_a}
\ge(q-1)\mathbb E_p\log p_a.
$$
除以负数 $1-q$ 反向即得结论。因此命题 4.6.6 的 $H_{3/2}>\log2$ 也认证了该例的 Shannon 严格条件。证毕。

阶二比较的既有声明 `CollisionShannonComparison.collision_entropy_le_shannon_entropy` 只承担 $q=2$ 情形；一般 $q$ 比较、$q\downarrow1$ 的微分极限和有效搜索分别由上面证明。没有从它们推出必要或锐的 iid 阈值，也没有从尚未结束的搜索推出反例。

### 4.7 Perron 回返权、数量化算法与原生编码运输

**定义 4.7.1（全部有限阶的回返根律）。** 对整数 $k\ge2$，令 $\lambda_k\in(1,2)$ 满足
$$
F_k(\lambda_k)=1,\qquad F_k(z)=\sum_{r=0}^{k-1}z^{-r-1},
\qquad p_r=\lambda_k^{-r-1}\quad(0\le r<k).
$$
$F_k$ 在正轴严格递减，$F_k(1)=k>1$、$F_k(2)=1-2^{-k}<1$，故中值定理与严格单调性给根的存在唯一性。它也是整系数多项式 $z^k-z^{k-1}-\cdots-1$ 的该区间唯一根；有理端点符号检验和二分隔离可以计算其任意精度名字。若某次有理中点恰为根，多项式的有理代入可精确识别并直接返回该根，因此计算不依赖无法终止的实数等号测试。

各 $p_r>0$、和为一，$p_{\max}=p_0=\lambda_k^{-1}<1$。在块字母空间 $Y_k=\{0,\ldots,k-1\}^{\mathbb N_0}$ 上直接取 iid 律 $\mu_p$。块 $r$ 表示从回返状态零开始的原始词 $1^r0$，时长 $r+1$。对块词 $v$，定义
$$
d=|v|,\qquad L(v)=\sum_{i<d}(v_i+1),\qquad
d\le L(v)\le kd,
\qquad \mu_p([v])=\prod_{i<d}p_{v_i}=\lambda_k^{-L(v)}\le p_{\max}^d.
$$
这些质量严格正且统一可计算，同块深度一般不相等，不能改成 $k^{-d}$。第 1.4.8 节已从初态零的 Perron 转移沿回返块望远镜相乘，识别这份 iid 律；任意位置的平稳初始混合并不是本定义的输入。

令最终 c.e. 禁块库存每个正块深度至多一词，不含根，可重复公告，定义 $E=Y_k\setminus\bigcup_{v\in\mathcal P}[v]$、$M=\mu_p(E)$、$R(v)\iff E\cap[v]\ne\varnothing$。所有接口均针对这一同一库存、同一 $E$ 及同一律。有限阶段按有限计算时间取已公告库存，不等待下次新事件。

**定理 4.7.2（全部 $k\ge2$ 的四概率接口）。** 在定义 4.7.1 上，仅附加承诺 $M>0$，四概率接口 $\mathbf M,\mathbf C,\mathbf T,\mathbf S$ 已均匀等价，$\mathbf R\to\mathbf M$ 也均匀成立，无需局部间隔或球对称均匀权重假设。

**证明。** 对真实深度 $n$ 延拓集，记
$$
A_n=\bigcup_{|v|=n,\,R(v)=1}[v],\qquad
a_n=\sum_{|v|=n,\,R(v)=1}\lambda_k^{-L(v)}.
$$
命题 4.3.6 给
$$
0\le a_n-M\le\sum_{h>n}p_{\max}^h
=\frac{p_{\max}^{n+1}}{1-p_{\max}}.
$$
这个界在浅层可以超过一，仍是合法上界。从可计算 $p_{\max}<1$ 搜索有理 $p_{\max}<q<1$，再按要求搜索 $n$ 使 $q^{n+1}/(1-q)$ 足够小，得到有效外部体积选择器。层列表有 $k^n$ 个词，其实际权重全部可计算。因此定理 4.1.4 适用，并且
$$
M\le D_n^{-1}\le M+\frac{p_{\max}^{n+1}}{1-p_{\max}},
\qquad D_n=\max_{|v|=n}\frac{\nu([v])}{\lambda_k^{-L(v)}}.
$$
第 4.2 节给四概率接口，命题 4.3.1 给延拓的反向算法。这里没有用“无禁祖先足以延拓”，也没有给每个非空切片正质量。所有参数均以完整块深度计，$k=2$ 也包含在内。证毕。

**命题 4.7.3（平方和恒等式与原有八分之一间隔）。** 对 $k\ge3$，令 $c_k=\sum_{r<k}p_r^2$，则
$$
c_k=\frac{3-\lambda_k}{1+\lambda_k}<\frac37<\frac12,
\qquad
\eta_k=1-\sqrt{\frac{c_k}{1-c_k}}
=1-\sqrt{\frac{3-\lambda_k}{2(\lambda_k-1)}}>\frac18.
$$
有最终禁祖先的柱切片为空；其余柱 $D$ 满足 $\mu_p(E\cap D)\ge\eta_k\mu_p(D)>\mu_p(D)/8$，特别 $M>1/8$。

**证明。** 置 $a=\lambda_k^{-1}$。由 $\sum_{j=1}^k a^j=1$，乘以 $1-a$ 得 $a-a^{k+1}=1-a$，故 $a^{k+1}=2a-1$。平方和完整化简为
$$
\begin{aligned}
c_k&=\frac{a^2-a^{2k+2}}{1-a^2}
=\frac{a^2-(2a-1)^2}{1-a^2}\\
&=\frac{(1-a)(3a-1)}{(1-a)(1+a)}
=\frac{3a-1}{1+a}
=\frac{3-\lambda_k}{1+\lambda_k}.
\end{aligned}
$$
又
$$
F_k(9/5)\ge\frac59+\frac{25}{81}+\frac{125}{729}
=\frac{755}{729}>1,
$$
所以 $\lambda_k>9/5$，代入严格递减的 $(3-z)/(1+z)$ 得 $c_k<3/7$。因此
$$
\sqrt{\frac{c_k}{1-c_k}}<\frac{\sqrt3}{2}<\frac78;
$$
最后的严格号平方后正是 $48<49$。第 4.6 节平方倾斜及局部化适用于同一 iid 律、同一正块深度预算，遂给两个局部分支；空词没有禁祖先，给根结论。证毕。

各深度最大柱质量的粗和不能代替这个前缀不交估计：此处 $p_0>1/2$，其正深度几何和已经大于一，无法供应上述正余量。$\eta_k$ 和 $1/8$ 在这里均未被证明最优。

**推论 4.7.4（六分之一的严格加强）。** 对全部 $k\ge3$，同一个 $\eta_k$ 实际满足 $\eta_k>1/6$。因此没有最终禁祖先时 $\mu_p(E\cap D)>\mu_p(D)/6$，而有祖先时仍为空；特别 $M>1/6$。

**证明。** 在更高的有理点上，
$$
F_k(57/31)\ge\frac{31}{57}+\frac{31^2}{57^2}+\frac{31^3}{57^3}
=\frac{185287}{185193}=1+\frac{94}{185193}>1,
$$
故 $\lambda_k>57/31$。令 $f(z)=(3-z)/(2(z-1))$，则
$$
f'(z)=-\frac1{(z-1)^2}<0,\qquad f(57/31)=\frac9{13},
\qquad \frac{25}{36}-\frac9{13}=\frac1{468}>0.
$$
从而 $c_k/(1-c_k)=f(\lambda_k)<9/13<25/36$，其平方根小于 $5/6$，即 $\eta_k>1/6$。局部结论沿用命题 4.7.3 的同一平方倾斜证明。证毕。

**定理 4.7.5（保留八分之一预算的单次质量查询算法）。** 输入 $k\ge3$、定义 4.7.1 的完整可计算呈示和一个 $M$ 的 Cauchy 名，可统一输出全部 $R(v)$。对合法词 $v$，使用
$$
g_v=2^{-L(v)-3},\qquad t=L(v)+7
$$
时只需一次指数为 $t$ 的质量名查询。若只使用块深度 $d$，可改用 $g=2^{-kd-3}$ 和 $t=kd+7$。

**证明及实现精度。** 因 $\lambda_k<2$，
$$
\mu_p([v])=\lambda_k^{-L(v)}\ge2^{-L(v)},
$$
空词等号，非空词严格。命题 4.7.3 因而给切片质量为零或严格大于 $g_v$。取所示 $t$，则 $2^{-t}=g_v/16$；读取一次 $v_M(t)$ 后置 $\ell_t=v_M(t)-2^{-t}$，有
$$
0\le M-\ell_t\le g_v/8.
$$
令 $E_s$ 为前 $s$ 计算步骤所见禁柱并的补集，$f_s=\mu_p(E_s)$、$u_s=\mu_p(E_s\cap[v])$。有限柱及有限并质量均是可计算实数，通常为非有理代数数；每个阶段通过前缀压缩或共同深度分割计算，不能把它们当作精确有理计数。

将定理 4.3.5 以 $g=g_v$ 具体代入：每阶段以误差小于 $g/48$ 求 $f_s$ 的有理近似，再加 $g/48$，形成
$$
f_s\le F_s<f_s+g/24.
$$
按有理比较寻找 $F_s-\ell_t<g/3$。因为
$$
F_s-\ell_t<f_s-M+g/24+g/8=f_s-M+g/6,
$$
且 $f_s\downarrow M$，它必在某有限阶段成功。局部化区间使 $0\le u_s-\mu_p(E\cap[v])<g/3$。最后计算有理 $u$，误差 $|u-u_s|<g/12$；空时 $u<5g/12<g/2$，非空时 $u>11g/12>g/2$。因此比较 $u>g/2$ 即为精确决定，不等待“以后不会再公告祖先”的否定证书。

非法块词直接返回否；根没有允许的禁祖先且 $M>1/8$，可直接返回是，也可按 $L=0,g=1/8,t=7$ 执行同一算法。若用 $kd$ 代替 $L(v)$，因 $L(v)\le kd$，相同严格间隔仍成立，全部误差分配不变。证毕。

推论 4.7.4 的加强没有改变这个算法。所示 $L(v)+7$ 或 $kd+7$ 是质量请求精度，不是公告等待或运行时间界；还要计算根、整理有限禁柱并、近似实数质量，并读取质量名返回的有理数。返回值的位长也属于实际成本。

**定理 4.7.6（加权反向算法、相对等价与点选择）。** 对 $k\ge3$，给 $k$、Perron 参考律及 $R$，无须禁词呈示即可计算 $M$。请求误差 $2^{-m}$ 时，选择 $n$ 使
$$
\frac{(5/9)^{n+1}}{1-5/9}<2^{-m-1},
$$
对全部 $k^n$ 个深度 $n$ 词查询 $R$，把实际加权和 $a_n$ 计算到误差严格小于 $2^{-m-1}$ 即可。

**证明。** 由 $\lambda_k>9/5$ 及命题 4.3.6，
$$
0\le a_n-M\le\frac{\lambda_k^{-(n+1)}}{1-\lambda_k^{-1}}
<\frac{(5/9)^{n+1}}{1-5/9}.
$$
选 $n$ 的搜索使用有理几何界且终止。每个正回答的项为 $\lambda_k^{-L(v)}$；例如每项数值误差小于 $2^{-m-1}/k^n$，总数值误差便小于 $2^{-m-1}$。两项之和小于 $2^{-m}$，给所需名字。查询数 $k^n$ 是这一算法的成本，不是最优下界；不能以 $|R_n|k^{-n}$ 代替 $a_n$。

结合定理 4.7.5 和第 4.2 节，在每个固定可计算呈示上，对每个 oracle $A$，质量为 $A$-可计算当且仅当延拓为 $A$-可判定，五接口统一互算。正向需要同一呈示，反向只需要参考模型和 $R$；若呈示另有 oracle，仍须显式保留该访问。任意质量名中的额外信息不受这个相对等价约束。

根有幸存者，从每个已延拓父词的有限孩子中选择首个延拓者，便计算一条相容无限串；闭性保证该串属于 $E$。这只使用 $R$ 的正确性，不能反推一个给定可计算幸存点就能计算全部 $R$。第 2.7.6 节的显式可计算点与困难延拓共存例仍给这一一般反向误推的边界。证毕。

同一参考律上若另有来源仅供应 $E=\operatorname{supp}\nu$，命题 4.3.3 的两个半判定也能加入 $R$；它不提供定理 4.7.5 的 $\mu_p([v])/8$ 精度预算。若供应可计算 $\eta>0$ 且非空切片质量至少 $\eta\mu_p([v])$，则用 $c_v=\eta\mu_p([v])$ 调命题 4.3.2。命题 4.7.3 的严格下界尤其允许取非严格供应 $c_v=\mu_p([v])/8$。各路线的凭据是它们实际证明的局部结论，不能只从 $k\ge3$、总质量正或编码名称取得。

**命题 4.7.7（每个固定非退化二元 iid 律的四输入相同家族）。** 固定可计算 $0<p_0,p_1<1$、$p_0+p_1=1$，取其二元 iid 参考律。存在一族每正深度至多一禁词的统一可计算呈示，具有相同的 $\mathbf M,\mathbf C,\mathbf T,\mathbf S$ 名字或机器，但不能由呈示索引与这些共同输入统一判定 $R$。每个固定实例的 $R$ 却可判。

**证明。** 对机器 $e$ 始终公告 $[0^n1]$，$n\ge1$；若机器停机再公告 $[0]$。每个正深度至多一个词，且
$$
E_e=
\begin{cases}
[1],&e\text{ 停机},\\
[1]\cup\{0^\infty\},&e\text{ 不停机}.
\end{cases}
$$
因为 $\mu_p(\{0^\infty\})=\lim_n p_0^n=0$，对所有 Borel 集 $B$ 都有
$$
M_e=p_1,\qquad
\nu_e(B)=\frac{\mu_p(B\cap[1])}{p_1}.
$$
具体柱公式为
$$
\nu_e([\varnothing])=1,\qquad
\nu_e([0v])=0,\qquad
\nu_e([1v])=\prod_{i<|v|}p_{v_i}.
$$
故一份固定的 $p_1$ Cauchy 名及一份固定的柱概率程序适用于全部 $e$。精确公平位采样器先输出字母 $1$，再按 $p$ 生成 iid 尾；可用定理 4.2.4 的相容区间细分实现。可数端点集为零测集，所以几乎必然无限生产；没有断言一般期望位成本有限。

规定阶段 $s$ 公告前 $s$ 个固定禁词并模拟机器 $s$ 步。若此时未发现停机，剩余集恰为 $[1]\cup[0^{s+1}]$，于是其质量精确为
$$
m_{e,s}=p_1+p_0^{s+1},\qquad
m_{e,s}-M_e=p_0^{s+1},\qquad
 d_{\mathrm{TV}}(\nu_{e,s},\nu_e)
=\frac{p_0^{s+1}}{p_1+p_0^{s+1}}\le\frac{p_0^{s+1}}{p_1}.
$$
发现停机后剩余集就是 $[1]$，误差为零。由固定概率名搜索固定有理 $p_0<q<1$、$0<\ell<p_1$，取 $g(j)$ 为首个满足
$$
q^{s+1}/\ell\le2^{-j}
$$
的 $s$；有理几何搜索终止，并给全家族同一个总变差选择器。

但 $R_e(0)=1$ 当且仅当机器不停机。统一恢复器若存在，以可由 $e$ 构造的呈示和上述四个完全相同的输入运行，就决定不停机，矛盾。固定 $e$ 时，两种延拓程序分别是“空词或首位一”，以及再加“全零词”，故各自可判。这只否定跨呈示统一恢复，没有断言其他固定加权二元呈示的点态分类。证毕。

**推论 4.7.8（黄金回返权的明确端点）。** 当 $k=2$ 时，$\lambda_2=\phi=(1+\sqrt5)/2$，$p_0=\phi^{-1}$、$p_1=\phi^{-2}$。命题 4.7.7 给共同质量 $\phi^{-2}$、相同全部条件概率与采样器、相同有效总变差选择器，但不能统一恢复零块柱的延拓。

**证明。** $\phi^2=\phi+1$ 给 $\phi^{-1}+\phi^{-2}=1$，故满足命题的固定可计算非退化二元律条件。其非停机实例中的全零块点质量为 $\lim_n\phi^{-n}=0$，但它确实延拓零块柱。顺便，由 $5<49/9$ 得 $\phi<5/3$，故
$$
c_2=\frac{3-\phi}{1+\phi}>\frac12.
$$
平方充分条件在此不成立；恢复失败的证明来自实际家族的非停机查询，而不是来自该充分条件失败。证毕。

这里的 $0,1$ 是块字母；通过回返编码，块 $1$ 是整个原始词 $10$。第 4.4 节的等权最终二进尾家族具有 $1-w_d/2$ 的质量、有限 clopen 拒绝采样和 $g(k)=k$ 的合同；本命题固定的是任意非退化二元 iid 权重，不能把两者合并成未经证明的任意 iid 分类。等权规范深度展开的逐点定理也不能直接移到这些非均匀权重上。

**命题 4.7.9（同一概率及任意有限窗口的运输）。** 使用第 1.4.2–1.4.3 节的可计算同胚
$$
\Phi_k(y)=1^{y_0}0\,1^{y_1}0\cdots:Y_k\longrightarrow X_k,
\qquad X_k=\{x\in\{0,1\}^{\mathbb N_0}:x\text{ 不含 }1^k\},
$$
及其在每个零后切块的逆 $\Psi_k$。令 $\rho_k^P=(\Phi_k)_*\mu_p$、$F=\Phi_k(E)$。则 $\rho_k^P(F)=M$，禁块呈示及其概率接口可按完整窗口对应运输。

**证明及窗口公式。** 第 1.4.2 节给出逐点有效双向编码：前 $N$ 块足够计算前 $N$ 原始位，前 $kn$ 原始位足够读出前 $n$ 块；此处引用其同一有限 $k$、同一有锚合法载体及唯一分解。对块词 $a$，记 $W(a)=1^{a_0}0\cdots1^{a_{|a|-1}}0$。其柱像为 $X_k\cap[W(a)]$，故禁柱并精确运输，推前定义给同一质量。

每个合法原始词唯一写成 $w=W(a)1^j$，$0\le j<k$。完整窗口 $j=0$ 的原像为 $[a]$；未完成窗口 $j>0$ 的原像为不交并 $\bigsqcup_{r=j}^{k-1}[ar]$。因而
$$
R_B(a)\iff R_X(W(a)),\qquad
R_X(W(a)1^j)\iff
\begin{cases}
R_B(a),&j=0,\\
\displaystyle\bigvee_{r=j}^{k-1}R_B(ar),&1\le j<k.
\end{cases}
$$
非法原始词返回否；这些等式包括空词、没有完整块的短词及最大未完成 run。它们是纯集合对应，不依赖赋权；概率运输还须使用同一推前律。参考窗口概率具体为
$$
\rho_k^P([W(a)1^j]_{X_k})
=\lambda_k^{-L(a)}\sum_{r=j}^{k-1}p_r
=\lambda_k^{-|w|}h_j,
\qquad h_j=\sum_{\ell=1}^{k-j}\lambda_k^{-\ell},
$$
$j=0$ 时 $h_0=1$。最终条件概率亦由相同有限不交并求和得到，最终原始条件律就是块条件律的推前。证毕。

未完成 run 不能任意补零：第 1.4.3 节的 $X_3$ 前缀 $1$ 同时允许块 $10$ 和 $110$；改成 $10$ 会删除后者。只有最大 run 的下一零被合法性强制，此时集合相同仍不表示实际读取事件、记录长度和位置成本相同。该节的 $(a,j)$ 档案、来源及协议时长条件继续适用。

**命题 4.7.10（实际时钟、一步操作与位置权重）。** 令 $S$ 删除一个块符号，$\sigma$ 删除一个原始位，$T(x)=\sigma^{(\Psi_kx)_0+1}x$。沿用第 1.4.4 节的操作，有
$$
\Phi_kS=T\Phi_k,\qquad
\Phi_k(S^ny)=\sigma^{L_n(y)}\Phi_k(y),\qquad
L_n(y)=\sum_{i<n}(y_i+1),
$$
$$
n\le L_n(y)\le kn,\qquad
L_{m+n}(y)=L_m(y)+L_n(S^my).
$$
原始单位步运输到块坐标后是
$$
D(y_0,y_1,\ldots)=
\begin{cases}
(y_1,y_2,\ldots),&y_0=0,\\
(y_0-1,y_1,y_2,\ldots),&y_0>0,
\end{cases}
\qquad \Phi_kD=\sigma\Phi_k.
$$
对任意指定原始位置权重 $(\omega_i)$，有限词 $w=W(a)1^j$ 的加权数值为
$$
\sum_{i<|a|}\sum_{h=0}^{a_i-1}\omega_{L_i(a)+h}
+\sum_{h=0}^{j-1}\omega_{L_{|a|}(a)+h},
\qquad L_i(a)=\sum_{t<i}(a_t+1).
$$

**证明。** 前述时钟和操作等式正是第 1.4.4 节的回返及倒计时对应：删除完整首块经过 $y_0+1$ 个原始步，删除单个位则在首块内部倒计时或移至下一块。累加实际屋顶时长给 $L_n$ 及 cocycle 恒等式。位置权重式逐个列出每个完整块的一位位置，再列出未完成 run 的一位位置，零位不贡献；因此原始位置没有被块下标替换。这也保留了第 1.3.6 节完整块加终端尾的精确状态、成本与时长等式。证毕。

A 卷第 2.17 节的加权继续任务定理在这里要求同一套继续测试、双向合法性、保持拼接的统一测试双射、状态转移交织、相同终端观察及可消去交换幺半群中的可加成本和原始时长。第 1.3.6 节以完整块加终端尾供应这些条件；只保留完整块的骨架缺少中途停止测试。实际合法测试拼接后须重新作唯一分块，成本和时长按原始边累加，才能调用该定理。指定 $\omega_i=F_{i+2}$ 给黄金整数的位置求值；其他 $k$-bonacci 数值权重仍须另行指定。赋给每块单位时间或直接用块下标作原始位置，是另一任务。

**命题 4.7.11（按原始深度计费不能直接代替块预算）。** 原始合法柱族
$$
[0]_{X_k},[10]_{X_k},\ldots,[1^{k-1}0]_{X_k}
$$
在各原始深度 $1,\ldots,k$ 分别只有一个柱，却覆盖整个 $X_k$；其块像在同一深度一包含全部 $k$ 个柱，因此违反本节预算。

**证明。** 每个 $X_k$ 点的首个零在前 $k$ 位内，零前一的数目唯一确定它所在的一个所列柱；不同数目对应的柱互不相交。逆分块后，它们正是首块符号 $0,\ldots,k-1$ 的各柱，全部在块深度一。故“原始每层一个”并未成为“块每层一个”。反向失败也由第 1.4.7 节的同一具体例子给出：块词 $(1)$、$(0,0)$ 深度一、二不同，展开 $10,00$ 却都长两位。证毕。

因此质量、操作、时钟和预算各有自己的运输式。这里的根律不是平稳 Parry 原始位置律；第 1.4.8 节已由初态及移位概率区分它们，并给出每块熵除以平均原始长度的比较。度量亦按第 1.4.2.1 节的实际首差位置运输：
$$
2^{-(k-2)}d_{\mathrm{block}}(y,z)^k
\le d_{\mathrm{raw}}(\Phi_ky,\Phi_kz)
\le d_{\mathrm{block}}(y,z).
$$
那里的共同长块例排除逆向统一 Lipschitz 常数；此处未把可计算同胚说成等距或等成本。

有限 $k$ 的全空间解析与第 1.4.9 节的无限字母边界也不能混用。$\Phi_\infty$ 只到有无穷多个零的非闭回返域，不包括最终全一串；逆算法在该域内等待下一零，没有只由块数决定的统一原始读取界。该节保留的两种概率极限不同：均匀块根律在原始空间趋于 $\delta_{1^\infty}$，Perron 根律趋于公平二进律。后者由无限几何块权生成的满测度对应，不扩张成完整紧二进空间的拓扑同胚。本节的所有正间隔及有限层查询结论都保持有限 $k$、完整块预算和固定回返初态这些域条件。

### 4.8 适用条件、数学来源与未覆盖的问题

#### 4.8.1 概率、支撑与有效性的来源范围

加权有限分割的密度夹逼见数学稿《稀疏禁柱的质量、条件律、有效逼近与采样：统一接口及其边界》第 9 节；非均匀实权重的完整有效除法及倒数误差见《非均匀有限分割中的条件律、质量恢复与编码接口》第 2–2.1 节。第 4.1 节将这两部分放在同一个概率空间和同一外部体积合同下。等权独有的整层查询算法保留在定理 4.4.2；第 2.5.2 节的三进外体积与后验上确界是相同有限加权平均思路的既有具体应用。

概率归一化、Doob 条件转移及密度计算的既有对象见第 2.10.4–2.10.6 节；停止流与 canonical 次概率见第 2.10.8–2.10.9 节。第 4.2 节所需有限字母、同一 oracle 和非有理阶段的适配均明确写出，未借三进特例的 $1/2$ 数值界代替一般的 $M>0$。一般局部质量的来源为第 2.3.2–2.3.3 节及第 2.7.2 节；第 4.3 节另保留真实延拓所需的间隔或支撑条件。

关于概率律与公平随机计算，直接文献是 Ackerman–Freer–Roy，[*On the Computability of Conditional Probability*, arXiv:1005.3014v4](https://arxiv.org/abs/1005.3014v4)：其 PDF 第 10 页固定公平 iid 输入，第 13 页 Proposition 2.18 给 $\mathbf S\to\mathbf C$，并归于 Galatolo–Hoyrup–Rojas（2010） 的 Proposition 2.4.2；Proposition 2.19 给 $\mathbf C\to\mathbf S$，并归于 Hoyrup–Rojas 的 Theorem 5.1.1。这里使用这两条采样箭头；有限 clopen 条件化由本章直接计算，不由其他条件分布定理省去额外假设。

Hoyrup–Rojas，[*Computability of probability measures and Martin-Löf randomness over metric spaces*, arXiv:0709.0907v2](https://arxiv.org/abs/0709.0907v2)，PDF 第 19–23 页 Definitions 5.0.1–5.0.2、5.1.1 及 Theorem 5.1.1，讨论可计算概率空间及带可计算 Cantor 测度 $\mu_\delta$ 的几乎处处同构。这个 Cantor 测度不应直接认作公平硬币律；定理 4.2.4 对公平源所需的方向由其明确区间构造承担。

Pauly–Fouché，[*How constructive is constructing measures?*, arXiv:1409.3428v1](https://arxiv.org/abs/1409.3428v1)，PDF 第 2–4、8–9 页的表示空间、开集及 overt 信息框架中，Theorem 25 的正向支撑关系给出：开集与支撑相交当且仅当该开集概率严格正。本章仅使用这份正信息。命题 4.3.3 的负判定另来自可计算 clopen 阶段和紧致性；该文的逆向构造并不提供这里指定的条件律、归一化常数或概率精度预算。

Bienvenu–Porter，[*Deep $\Pi^0_1$ Classes*, arXiv:1403.0450v3](https://arxiv.org/abs/1403.0450v3) 的 Remark 2.2 和作者明确标作 folklore 的 Lemma 3.5，按第 2.10.8 节与第 2.3 节所保留的原文及证明范围使用：前者连接几乎必然持续输出与可计算律，后者的证明给局部质量计算及正质量点选择。有限变化字母表的算法合同由本章及第 2.3.3 节承担，不将这些更具体措辞逐字归于文献。

#### 4.8.2 前缀估计与仓内数学接口

平方倾斜的前缀估计及 Perron 具体算法见《Perron 回返概率下的稀疏禁柱：正间隔与有效延拓》第 2–7 节；一般 Hölder 倾斜、Shannon 极限与参数搜索见《Rényi 熵下的稀疏前缀间隔与有效参数搜索》第 2–5 节。平方上界对应前一数学稿第 2 节命题 2.1 的不等式，倾斜字母定义和柱乘积身份是其证明的输入，不是另一个上界。第 4.6 节的共同证明以标准 Hölder、Jensen、柱概率可加性及有限测度连续性为工具，所有具体模型前提均在正文履行。

可数 Hölder 的直接仓内来源为 [CountableWeightedHolderInterpolation](../../../D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation.lean) 的 `countable_weighted_holder_interpolation`。它要求非负可和实函数和正互补指数；定理 4.6.2 的辅助柱不交与长度几何和分别履行两个可和性条件。

[PrefixFreeCode](../../../D5/S0/Computability/Coding/PrefixFreeCode.lean) 的 `kraft_inequality_of_isPrefixFree` 与 [KraftInequality](../../../D5/S0/Computability/KraftInequality.lean) 的 `finite_binary_kraft_inequality` 处理有限二元均匀权 $2^{-|w|}$，分别使用适当的无空词前缀自由或唯一可译码前提。它们没有提供任意非均匀可数倾斜族的概率界。有限码唯一可译码性可由经典 Sardinas–Patterson 算法以有限剩余后缀状态判定；这一性质不能被说成有限情形不可检查。相应经典来源是 A. A. Sardinas and G. W. Patterson，*A necessary and sufficient condition for the unique decomposition of coded messages*，1953。

[CollisionShannonComparison](../../../D5/S3/QuantumBounds/CollisionShannonComparison.lean) 的 `collision_entropy_le_shannon_entropy` 适用于有限非负归一化概率，给阶二碰撞熵不超过 Shannon 熵；其等号描述是正支撑上的均匀性。任意 $q>1$ 的比较与趋一极限由命题 4.6.7 和定理 4.6.5 分别承担。

[MarkovPrefixMass](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.lean) 的 `markov_chain_law_map_prefix_apply_singleton` 以概率初始测度、Markov 核及可测单点为前提，给长度 $n+1$ 的非空单点前缀质量。对有限离散字母，取初态律为 $p$、从每个当前字母出发的核均为 $p$，便得到本章 iid 前缀乘积；空词的质量一单独来自归一化。该来源保留其 Tau Ceti 来源及 Apache-2.0 许可证归属；它不供应回返编码、根初态识别、平稳性或预算运输。

回返编码及初态识别的具体来源是本卷第 1.4.2–1.4.9 节，关联 Context Geometry 定理 9.18、式（9.18）—（9.20）与 RRO 主文定理 33.9–33.10 的根律及平稳律区分。W. Parry 的 [*Intrinsic Markov chains* (1964)](https://doi.org/10.1090/S0002-9947-1964-0161372-1) 按这些既有章节的归属使用；本章所需的回返权与窗口等式由该处转移公式及这里的同一模型计算承担。

#### 4.8.3 有限支持、几乎处处关系与共同实现

[ConditionalInformationSufficiency](../../../D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency.lean) 的 `conditional_information_zero_iff_support_sufficiency` 针对有限状态、概念、目标及同一个先验和通道形成的联合律。零条件互信息对应条件独立及概念纤维内正先验状态上的核恒定；零先验状态不受这份结论约束。这种有限先验支持不是命题 4.3.3 的无限路径空间拓扑支撑，也未提供后者的有效闭负测试。

[PositivePriorConditionalIndependence](../../../D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence.lean) 的 `positive_prior_sufficiency_iff_conditional_independence` 要求有限状态上的先验逐点严格正，才把同一联合律的条件独立提升到全部状态的核分解 $K=\overline K\circ\operatorname{concept}$。概念域可以另行给定，但因子的存在不自带可计算性、继续操作保持、环境组合或最小性。不能删去逐点正先验来处理本章的零质量分支。

[PointwiseAlmostEverywhereSeparation](../../../D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.lean) 的 `pointwise_sufficient_implies_almost_everywhere_sufficient` 以非空目标为前提，把纤维恒定扩成全读数域上的因子；其 `fpod_principle_118_1` 用常值读数和只在实数零点为真的目标，在非零 Lebesgue 测度下分离逐点与几乎处处充分。原例使用非概率测度，因子定义也没有加入可测或可计算保证，故不代替本章两种概率反例或公平随机机证明。该来源的恒等读数、常目标、零测度与空目标边界各保留在其原合同内。

[FiniteMarginalGlobalReadoutContrast](../../../D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast.lean) 的有限边缘相容、有限读数满射及 `readout_image_null` 结果，取自然数有限子集为源，读成二元有限支撑路径。任意有限坐标可实现，且共同公平乘积律的有限边缘相容，但完整读数像的概率为零；全路径恒等或满射读数则有全像。这一源像非闭，结论不否认全路径乘积概率或逆极限的存在。它说明有限共同读数不能自动认作指定源的全局实现，未供应第 4.5 节的观察度量、Dirac 反例或同一块对象的有效模量分离。

#### 4.8.4 条件的分工及尚未覆盖的范围

有效外部体积供应承担条件律反求总质量；缺少速率的外逼近或只有嵌套性不够，命题 4.4.5 给出同一对象上的失败。局部正间隔或精确支撑承诺承担概率信息恢复真实延拓；正总质量不能替代它们，命题 4.4.6 和命题 4.7.7 保留的零分支给出不同量词下的障碍。支撑路线没有数量化精度界，数量化路线也不把最终无祖先语义变成有限未见公告的证书。

变量进制的规范基、最终祖先及数值展开条件仍由第 2.9.2–2.9.8 节承担；非均匀 Perron 的四接口与 $k\ge3$ 局部间隔由第 4.7 节在其明确新权重合同中给出，不改变原均匀定理的假设。第 2.7.7 节的两个一般有效闭反例仍分别展示非空零切片和可计算实数零测试的困难，不能因标题相近而替换本章独立块或二元家族的证明。

Rényi 或 Shannon 严格条件是充分路线。一般 iid 概率向量的必要或锐条件、不同深度预算、非 iid 过程、原始位置平稳 Parry 初始混合、最优间隔常数与最优算法成本，均不在这些定理的结论中。某个倾斜指数不合格、$H(p)\le\log2$，或某次证书搜索尚未结束，都不推出某个具体库存质量为零。单个库存也可以比统一预算界保留更多质量。有限字母、严格正概率、共同 iid 尾、无根禁词、有限前缀压缩及每正层一词分别参与证明，改变任一条件都须重新证明所需箭头。

最后，层深、概率精度、公告阶段、已完成块数、原始时长、名字位长和随机采样等待是不同资源。可计算性等价不宣称复杂度等价；点选择也不等于所有点的成员判定。第 2.1–2.8 节关于有限候选与最终延拓、普通整数与完成线程、有限正认证和无限成功的区分继续适用，第 3.1 节关于有限一致性、有效证明生成、HALT 族和固定理论独立性的条件亦保持各自量词。这里的表示与恢复定理不推出有限互异奇模数覆盖结论、固定 E7 独立性、物理时钟定律或熵产生律。正质量和局部延拓间隔仍不提供对一个无限点仅凭有限数字的最终成员正认证。

## 追加锚（本行以下为增补区）

## 5. 正 iid 律的稀疏余量、深度预算与有效恢复

### 5.1 共同 iid 模型、实际深度预算与一致尾界

**定义 5.1.1（概率、码族与幸存集）。** 固定一个有完整有限列表的字母表 $\Sigma$，其实际大小为 $d\ge2$。在 $X=\Sigma^{\mathbb N_0}$ 上取同一个 iid 概率律 $\mu_p$，其中
$$
p_a>0\quad(a\in\Sigma),\qquad \sum_{a\in\Sigma}p_a=1,
\qquad m=m_p=\max_a p_a<1.
$$
严格不等式来自至少两个实际字母均有正权重。对有限词 $w$，写
$$
p(w)=\mu_p([w])=\prod_{i<|w|}p_{w_i},\qquad p(\varnothing)=1.
$$
给定非负整数序列 $b=(b_n)_{n\ge1}$，令 $\mathcal C_b$ 为所有前缀自由族 $\mathcal F\subseteq\Sigma^+$，满足 $|\mathcal F\cap\Sigma^n|\le b_n$。这里前缀自由指不同词互不为前缀，$\Sigma^+$ 排除空词；族可以有限或可数，可以跳过任意层。计数对象是最终不同的词，重复公告不重复计费。$b_n\equiv1$ 时简称一词预算，记可行族空间为 $\mathcal C_1$。

定义删除质量、最终幸存集与深度截断为
$$
S_{\mathcal F}(p)=f_{\mathcal F}(p)=\sum_{w\in\mathcal F}p(w),\qquad
E_{\mathcal F}=X\setminus\bigcup_{w\in\mathcal F}[w],
$$
$$
\mathcal F_{\le N}=\{w\in\mathcal F:|w|\le N\},\qquad
E_{\mathcal F,N}=X\setminus\bigcup_{w\in\mathcal F_{\le N}}[w].
$$
不同禁词的柱两两不交，故 $0\le S_{\mathcal F}(p)\le1$，$\mu_p(E_{\mathcal F})=1-S_{\mathcal F}(p)$。每个 $E_{\mathcal F,N}$ 是深度 $N$ 柱的有限并，$E_{\mathcal F,N}\downarrow E_{\mathcal F}$；这是一份集合论上的 clopen 外逼近，尚未声称能从任意公告程序计算其完整深度截断。

**定义 5.1.2（次指数预算）。** 预算次指数增长的含义恰为
$$
\forall a>1\ \exists N_0\ \forall n\ge N_0,\qquad b_n\le a^n.
$$
此存在量词不供应一个有效求出 $N_0$ 的程序。另记均匀律下的预算和
$$
B_d(b)=\sum_{n\ge1}b_nd^{-n}.
$$
第 5.2 节的全族正余量假设为 $B_d(b)<1$。它是预算在均匀概率 $u=(1/d,\ldots,1/d)$ 下的上界，与实际概率 $p$ 下某个族的删除质量不同。

**引理 5.1.3（全族一致的深度尾界）。** 若 $a>1$、$am<1$，且 $b_n\le a^n$ 对全部 $n\ge N_0$ 成立，则对任意 $\mathcal F\in\mathcal C_b$ 和 $N\ge N_0$，
$$
0\le S_{\mathcal F}(p)-S_{\mathcal F_{\le N}}(p)
=\mu_p(E_{\mathcal F,N})-\mu_p(E_{\mathcal F})
\le\sum_{n>N}b_nm^n
\le\frac{(am)^{N+1}}{1-am}.
$$
特别地，对一词预算和全部 $N\ge0$，有精确的几何尾表达式
$$
0\le S_{\mathcal F}(p)-S_{\mathcal F_{\le N}}(p)
=\mu_p(E_{\mathcal F,N})-\mu_p(E_{\mathcal F})
\le\frac{m^{N+1}}{1-m}.
$$

**证明。** 每个长度 $n$ 的词质量至多 $m^n$，该层至多 $b_n$ 项；逐层相加并求几何级数即得。质量差等式来自同一前缀自由族的柱可加性。次指数假设允许先选 $1<a<1/m$，再取其某个 $N_0$，所以第一尾界总能在充分大深度使用；这一尾界本身不需要 $B_d(b)<1$。一词情形直接求 $\sum_{n>N}m^n$，不引入额外的 $a$。证毕。

本章的深度始终是模型中实际词的长度。它不是公告发生的计算时刻，也不是另一次编码后的长度。即使最终每层只有一个词，短词仍可任意晚公告；上式控制长词总质量，不为尚未公告的短词提供截止时间。回返块若被用作字母，则这里的实际词长是块数，转回原始位须另用第 1.4 节及第 4.7.9–4.7.11 节的长度、窗口与预算合同。

### 5.2 满质量传播、最优族的取得与正余量分类

**定理 5.2.1（固定族的满质量不能只发生在部分正概率上）。** 固定次指数预算 $b$ 及 $\mathcal F\in\mathcal C_b$。在正概率单纯形
$$
\Delta_d^\circ=\{p\in\mathbb R^d:p_a>0,\ \sum_a p_a=1\}
$$
中，集合 $Z_{\mathcal F}=\{p:S_{\mathcal F}(p)=1\}$ 既相对闭又相对开。因此它或者为空，或者等于整个 $\Delta_d^\circ$。若另有 $B_d(b)<1$，则它为空。

**证明。** 先证相对闭性。固定 $p\in\Delta_d^\circ$，取 $m_p<r<1$，并缩小一个相对邻域，使其内每个 $q$ 都满足 $\max_a q_a\le r$。取 $1<a<1/r$，由次指数性选取相应 $N_0$。有限截断 $S_{\mathcal F_{\le N}}(q)$ 是坐标的多项式；引理 5.1.3 在此整个邻域上给尾界 $(ar)^{N+1}/(1-ar)$。故这些多项式局部一致收敛到 $S_{\mathcal F}$，该函数连续，$Z_{\mathcal F}$ 相对闭。

再设 $p\in Z_{\mathcal F}$，写 $m=m_p$，选择 $1<a<1/m$ 及其预算阈值 $N_0$。定义
$$
C(q,p)=\max_{a\in\Sigma}\frac{q_a}{p_a}.
$$
对任何长度 $N$ 的词 $v$，$q(v)\le C(q,p)^N p(v)$。集合 $E_{\mathcal F,N}$ 是同一批长度 $N$ 柱的有限不交并，因此
$$
\mu_q(E_{\mathcal F,N})\le C(q,p)^N\mu_p(E_{\mathcal F,N}).
$$
满质量前提使 $\mu_p(E_{\mathcal F})=0$，故对 $N\ge N_0$，
$$
\mu_q(E_{\mathcal F,N})
\le C(q,p)^N\frac{(am)^{N+1}}{1-am}
=\frac{am}{1-am}\bigl(C(q,p)am\bigr)^N.
$$
因为 $C(p,p)=1$ 且 $C(q,p)$ 关于 $q$ 连续，条件 $C(q,p)am<1$ 给出 $p$ 的一个相对邻域。在该邻域中令 $N\to\infty$，右侧趋零，而 $E_{\mathcal F}\subseteq E_{\mathcal F,N}$，故 $\mu_q(E_{\mathcal F})=0$。这证明相对开性。

正单纯形是凸集，因而连通；一个既开又闭的子集只能为空或全体。均匀向量 $u$ 满足
$$
S_{\mathcal F}(u)=\sum_{n\ge1}|\mathcal F\cap\Sigma^n|d^{-n}
\le B_d(b)<1,
$$
故 $u\notin Z_{\mathcal F}$，排除全体的可能。证毕。

证明比较的是有限深度的柱质量；不同参数的无限 Bernoulli 律不必互相绝对连续，不能用这种未成立的前提替换上述有限似然比和极限论证。到此得到的是每个固定族的严格不满质量；这还不足以推出对全部族共同的正余量。

**定理 5.2.2（紧致可行族与实际最大值）。** 对任意次指数预算和固定 $p\in\Delta_d^\circ$，最大值
$$
M_b(p)=\max_{\mathcal F\in\mathcal C_b}S_{\mathcal F}(p)
$$
实际取得。若 $B_d(b)<1$，则
$$
\eta_b(p):=1-M_b(p)>0,\qquad
\forall\mathcal F\in\mathcal C_b,\quad\mu_p(E_{\mathcal F})\ge\eta_b(p).
$$
量词为 $\forall p\in\Delta_d^\circ\ \exists\eta_b(p)>0\ \forall\mathcal F$，不是对全部正概率共同取同一个常数。

**证明。** 对每个 $n\ge1$，令
$$
\mathcal A_n=\{S\subseteq\Sigma^n:|S|\le b_n\}.
$$
这是非空的有限离散空间；即使 $b_n=0$，仍包含空集。乘积 $\prod_{n\ge1}\mathcal A_n$ 非空紧致。可行族对应其中跨层不发生前缀冲突的点；若有冲突，两条有限词及其两层坐标已是见证，保持这两个坐标的乘积开邻域全都冲突。因此可行子集闭，仍紧致且包含全空选择。

固定 $p$ 后，截断目标只依赖前 $N$ 个坐标，是连续函数。引理 5.1.3 的误差对全体可行族一致，故极限目标连续，必在某个 $\mathcal F_*$ 取得最大值。若 $B_d(b)<1$，定理 5.2.1 对这个实际 $\mathcal F_*$ 给 $S_{\mathcal F_*}(p)<1$，遂得所需余量。正是最大值的取得排除了“每族都严格小于一而上确界仍为一”的可能。证毕。

**推论 5.2.3（一词预算及常数预算的正方向）。** 记
$$
B(p)=\sup_{\mathcal F\in\mathcal C_1}S_{\mathcal F}(p),\qquad
\eta(p)=1-B(p).
$$
对全部 $d\ge2$，这个上确界实际取得，且 $B(p)=1$ 当且仅当存在一个合法满质量族。对 $d\ge3$，有 $B(p)<1$、$\eta(p)>0$。更一般地，整数常数预算 $b_n=c\ge0$ 在 $d\ge c+2$ 时具有同样的固定 $p$ 全族正余量。

**证明及参数代入。** 一词预算的单层选择可直接写为 $\Sigma^n\sqcup\{\bot\}$，其中 $\bot$ 表示跳过该层，不能删掉这个符号。跨层前缀违例仍是有限见证；一致尾现在恰为 $m^{N+1}/(1-m)$。因此定理 5.2.2 的紧致证明对 $d=2$ 也保证取得最大值，并给满质量族的等价。

定理 5.2.1 的一词专门化无需引入 $a>1$：在满质量点 $p$，直接有
$$
\mu_q(E_{\mathcal F,N})
\le\frac{m}{1-m}\bigl(C(q,p)m\bigr)^N,
$$
邻域条件为 $C(q,p)m<1$。均匀律的上界为
$$
\sum_{n\ge1}d^{-n}=\frac1{d-1}<1\qquad(d\ge3).
$$
这就履行了同一开闭证明的全部前提。常数预算的次指数性来自 $a^n\to\infty$，且 $B_d(b)=c/(d-1)<1$ 恰在整数条件 $d\ge c+2$ 下成立。其相反方向和 $c=0$ 端点见第 5.7 节。证毕。

### 5.3 可计算的最优值与两种一词余量算法

**定理 5.3.1（有限最大值的有效逼近）。** 给定有限 $d\ge2$ 和严格正归一化坐标 $p_a$ 的可计算实数名，可以统一计算 $B(p)$ 和 $\eta(p)$ 的 Cauchy 名。此断言也相对于任意共同 oracle 成立，不要求从一般可计算实数名中选出精确的最大化族。若 $d\ge3$，还可统一输出有理数 $0<\gamma<\eta(p)$。

**证明及算法。** 对每个 $N$，枚举 $\prod_{n=1}^N(\Sigma^n\sqcup\{\bot\})$，用有限词前缀检查保留全部合法选择，令其最大删除质量为 $B_N(p)$。枚举有限且可完成。每个候选值是 $p$ 的有限多项式，可计算到任意误差；把所有候选都算到误差 $\epsilon$ 后取有理最大值，误差仍至多 $\epsilon$。这计算的是最大值，不判断两个真实候选值是否相等，也不选择一个精确优胜者。

有限合法族可以在余下层全部选 $\bot$；无限合法族又可截断为有限合法族。两个方向分别给出
$$
B_N(p)\le B(p)\le B_N(p)+\frac{m^{N+1}}{1-m}.
$$
从坐标名求各 $p_a$ 的包含区间并提高精度；由于 $m<1$，最终全部上端均小于一，此时在最大上端与一之间取有理 $r$，得到严格的 $m<r<1$。于是可使用完全有理的尾
$$
T_N(r)=\frac{r^{N+1}}{1-r},\qquad
B_N(p)\le B(p)\le B_N(p)+T_N(r).
$$
为请求 $2^{-k}$ 精度，搜索 $N$ 使 $T_N(r)<2^{-k-2}$，再将 $B_N$ 近似到误差小于 $2^{-k-2}$，输出该近似即可；总误差小于 $2^{-k-1}$。对一减去此名给 $\eta$ 的名字。所有几何搜索因 $r<1$ 终止。

例如取 $|v_B(j)-B|\le2^{-j}$ 的名字，令 $U_j=v_B(j)+2^{-j}$。则 $U_j\ge B$、$U_j\to B$。在 $d\ge3$ 的严格余量承诺下，搜索有理条件 $U_j<1$ 必终止，并输出
$$
\gamma=\frac{1-U_j}{2},\qquad 0<\gamma<\eta(p).
$$
最后一个严格号即使 $U_j=B$ 仍由取半保证。以上转换在承诺域上运行，不先判定正性或归一化，也没有给有限枚举的多项式成本或对全部 $p$ 的共同正下界。证毕。

**定理 5.3.2（只用正坐标下界的余量构造）。** 在明确的 $d\ge3$ 条件下，只要给出正有理数
$$
0<\ell<\min\{1/d,\min_a p_a\},
$$
就能仅用 $d,\ell$ 和有理运算计算一个严格正的统一余量证书 $\gamma<\eta(p)$。可计算正坐标名可通过严格下界搜索供应这样的 $\ell$。

**证明及算法。** 置
$$
r=1-(d-1)\ell,\qquad c=1+\ell,\qquad
rc=1-(d-2)\ell-(d-1)\ell^2<1.
$$
有 $0<r<1$、$c>1$。选择整数 $J>\ell^{-2}$，令 $u=(1/d,\ldots,1/d)$，并在证明中使用
$$
q_j=(1-j/J)u+(j/J)p,\qquad 0\le j\le J.
$$
各坐标严格大于 $\ell$，由其余 $d-1$ 个坐标的下界知每项至多 $r$。相邻坐标之差的绝对值至多 $1/J$，故
$$
\frac{q_{j-1,a}}{q_{j,a}}
\le1+\frac1{J\ell}<1+\ell=c.
$$
固定任意 $\mathcal F\in\mathcal C_1$，写 $E=E_{\mathcal F}$。对深度 $N$ 的有限并作上述似然比比较，再用在 $q_j$ 下的尾界，得到
$$
\begin{aligned}
\mu_{q_{j-1}}(E)
&\le\mu_{q_{j-1}}(E_{\mathcal F,N})
\le c^N\mu_{q_j}(E_{\mathcal F,N})\\
&\le c^N\mu_{q_j}(E)+c^N\frac{r^{N+1}}{1-r}
=c^N\mu_{q_j}(E)+\frac{r(rc)^N}{1-r}.
\end{aligned}
$$
从均匀律的确定下界
$$
\gamma_0=1-\frac1{d-1}=\frac{d-2}{d-1}>0
$$
开始。对 $j=1,\ldots,J$，依次搜索整数 $N_j\ge1$ 使
$$
\frac{r(rc)^{N_j}}{1-r}<\frac{\gamma_{j-1}}2,
\qquad
\gamma_j=\frac{\gamma_{j-1}}{2c^{N_j}}.
$$
因 $rc<1$ 且 $\gamma_{j-1}>0$，每项有理严格搜索都终止。若对所有族已有 $\mu_{q_{j-1}}(E)\ge\gamma_{j-1}$，运输不等式便给
$$
\mu_{q_j}(E)>\frac{\gamma_{j-1}}{2c^{N_j}}=\gamma_j.
$$
归纳到 $q_J=p$ 得全族下界；特别 $\eta(p)\ge\gamma_J>0$，所以输出 $\gamma_J/2$ 严格小于 $\eta(p)$。实际计算不需要读取辅助 $q_j$ 的值，只用 $d,\ell,r,c,J$ 和上述有理递推；这些辅助律仅证明下界对目标 $p$ 有效，并未替换实际参考律。证毕。

$d\ge3$ 同时保证初始 $\gamma_0>0$；不能把本算法在二元情形形式地启动。$J$、各 $N_j$、有理数位长和有限优化规模都可能很大。定理 5.3.1 与 5.3.2 分别给最优值逼近和坐标下界路线，它们没有主张实用的统一快速估计。

### 5.4 贪心交换、整数递推与低熵实例

**定理 5.4.1（一词预算的有限及无限贪心最优性）。** 固定 $d\ge2$ 及同一正 iid 律。从深度一开始，在每层选择一个不在此前所选词之后的最大质量活词；并列时任选。任意这样相容地作出的前 $N$ 层选择都取得 $B_N(p)$，整个无限贪心族取得 $B(p)$。

**证明。** 深度 $n$ 的候选一定存在。此前每层至多一个词，故在 $d^n$ 个长度 $n$ 的词中，被此前选择遮住的词数至多
$$
\sum_{j=1}^{n-1}d^{n-j}=\frac{d^n-d}{d-1}<d^n.
$$
这个计数使用均匀的词数，只为保证存在，不把实际柱质量改成均匀权重。有限非空候选中总有最大质量词。

固定一个深度至多 $N$ 的最优族，并假设已使其前 $n-1$ 层与某条指定贪心运行一致。令本层贪心词为 $u$。若最优族本层已有 $u$，无需改变。若本层已有另一词 $v\ne u$，它也是活词，故 $p(u)\ge p(v)$；$u,v$ 同层，子树不交，旧族选了 $v$，所以旧族没有 $v$ 的真后代。令旧族在 $u$ 下的真后代为 $uz$，其尾族前缀自由，且
$$
\alpha=\sum_{uz\text{ 为旧族成员}}p(z)\le1.
$$
这里所有 $z$ 都按同一个 iid 尾律计算，所以 $p(uz)=p(u)p(z)$、$p(vz)=p(v)p(z)$。把 $v$ 换成 $u$，并把全部这些 $uz$ 换成 $vz$。尾族前缀自由使新 $vz$ 之间不冲突；旧 $v$ 子树没有其他选词，新 $u$ 的原有后代全部移走，其余子树不变。因此前缀自由性保留，各被移动词长度不变，每层预算不变，已对齐的浅层也不变。质量增益精确为
$$
\bigl(p(u)+p(v)\alpha\bigr)-\bigl(p(v)+p(u)\alpha\bigr)
=(p(u)-p(v))(1-\alpha)\ge0.
$$
若旧最优族跳过了深度 $n$，则添加 $u$ 并删除其所有已选真后代；以相同的尾质量 $\alpha\le1$ 计算，增益为
$$
p(u)-p(u)\alpha=p(u)(1-\alpha)\ge0.
$$
这个分支不增加其他层的词数，仍保留全部浅层选择。三种分支均把合法最优族变成与本层贪心相同、质量不下降的族；因原族已最优，改后也最优。逐层归纳到 $N$，即得有限贪心最优性。不能在归纳开始就假设最优族每层已选一个词，跳层分支正负责补足这一点。

现在从根起固定一条无限贪心运行 $\mathcal G$，并列选择保持前后相容。其每个有限截断都是相应有限问题的最优族，所以 $S_{\mathcal G_{\le N}}(p)=B_N(p)$。有限族可空层延长，无限族可截断，故引理 5.1.3 给 $B_N(p)\le B(p)\le B_N(p)+m^{N+1}/(1-m)$；这个夹逼不要求 $p$ 可计算。令 $N\to\infty$ 得 $S_{\mathcal G}(p)=B(p)$。证毕。

交换论证的关键是两个子树使用同一 iid 后缀质量 $\alpha$；对非 iid 律或任意其他层预算，没有在此证明相同贪心规则。若 $p$ 为有理数或给有精确表示的有效实代数数，可以精确比较有限乘积，包含等号时的并列处理，从而实现此贪心选择。一般可计算实数名只保证最大值可计算，不供应统一的精确 argmax 或精确最大化族选择器；定理 5.3.1 不消耗这种额外操作。

**命题 5.4.2（按稀有字母数递推的精确证书）。** 取整数 $d\ge3$、$a\ge b\ge1$，置
$$
D=a+(d-1)b,\qquad p=\frac1D(a,b,\ldots,b).
$$
把深度 $n$、已执行该层删除后的活词按其中稀有字母数 $r$ 分类，记数为 $C_n(r)$。初始化 $C_0(0)=1$，其余及越界下标的计数为零。扩展到下一层而尚未删除时，
$$
\widetilde C_n(r)=C_{n-1}(r)+(d-1)C_{n-1}(r-1).
$$
令 $r_n$ 为 $\widetilde C_n(r)>0$ 的最小下标，并设 $C_n(r_n)=\widetilde C_n(r_n)-1$，其他类不变。再令
$$
R_0=1,\qquad R_n=DR_{n-1}-a^{n-r_n}b^{r_n}.
$$
则有限最优幸存质量及全族无限余量满足
$$
M_N^{\mathrm{fin}}:=1-B_N(p)=\frac{R_N}{D^N},\qquad
\eta(p)\ge\frac{(D-a)R_N-a^{N+1}}{(D-a)D^N}.
$$
因此以下纯整数不等式证明 $\eta(p)>1/Q$：
$$
Q\bigl((D-a)R_N-a^{N+1}\bigr)>(D-a)D^N.
$$

**证明。** 每个活词有一个重字母孩子和 $d-1$ 个稀有字母孩子，分别给计数递推两项。含 $r$ 个稀有字母的词质量是 $a^{n-r}b^r/D^n$；$a\ge b$ 使最小非空类具有最大质量。若 $a=b$ 则全部并列，选最小类仍合法。相同类中具体位置不影响以后计数，因为每个词都有相同的 iid 子树扩展；这只计算值，并不重建所选词列表。

每次扩展保留前层总活质量；统一到分母 $D^n$ 后，旧分子乘 $D$，再减去本层所选词的分子，得到 $R_n$。定理 5.4.1 使此活质量等于有限最优幸存质量。以 $m=a/D$ 代入引理 5.1.3，
$$
\eta(p)\ge M_N^{\mathrm{fin}}-\frac{(a/D)^{N+1}}{1-a/D}
=\frac{(D-a)R_N-a^{N+1}}{(D-a)D^N}.
$$
因 $D-a=(d-1)b>0$，与 $1/Q$ 的严格比较可交叉相乘，正是所示整数证书。证毕。

**命题 5.4.3（三个严格低熵的正余量实例）。** 下列三元概率都满足 $H(p)<\log2$，但对全部合法一词族具有表列严格余量。十进制列仅展示数值，判定使用命题 5.4.2 的整数不等式。

| 实际三元概率 $p$ | $(a,b,D)$ | 深度 $N$ | $M_N^{\mathrm{fin}}$ 的十进制近似 | 几何尾的十进制近似 | 全族严格余量 |
|---|---|---:|---:|---:|---:|
| $(4/5,1/10,1/10)$ | $(8,1,10)$ | 22 | $0.0313976780752303423488$ | $0.0295147905179352825856$ | $\eta(p)>1/1000$ |
| $(9/10,1/20,1/20)$ | $(18,1,20)$ | 73 | $0.00441675839658733910867$ | $0.00411098316705696636583$ | $\eta(p)>1/10000$ |
| $(49/50,1/100,1/100)$ | $(98,1,100)$ | 729 | $0.0000200547878776184524391$ | $0.0000196791012345124677617$ | $\eta(p)>1/10000000$ |

**证明及可复现计算。** 按命题 5.4.2 从 $C_0,R_0$ 递推至各 $N$，分别代入 $Q=1000,10000,10000000$，三项整数证书均为真。低熵的检验也只需整数：
$$
DH(p)=D\log D-a\log a-(d-1)b\log b,
$$
$$
H(p)<\log2
\quad\Longleftrightarrow\quad
D^D<2^D a^a b^{(d-1)b}.
$$
这是将第一式与 $D\log2$ 比较后指数化；对上述参数三个严格整数不等式均成立。首例化为 $10^{10}<2^{34}$。

以下为完整的 Python 3 标准库程序，代码块内容的 SHA256 为 `f4bcd458d0ba0ea954a6606568698ce37ceee601cd63f1d113bf71efa7d7e690`。将其保存为 `iid-sparse-prefix-gap-experiment.py` 即可运行。其默认参数元组 $(a,b,d,N,Q)$ 是 $(8,1,3,22,1000)$、$(18,1,3,73,10000)$、$(98,1,3,729,10000000)$；也可分别用 `--a`、`--b`、`--d`、`--max-depth`、`--gap-denominator` 提供同形输入。

```python
#!/usr/bin/env python3
"""Exact sparse-prefix mass certificates for p=(a,b,...,b)/(a+(d-1)b).

The finite-horizon optimum is justified by the exchange theorem 5.4.1
in this chapter.
All acceptance decisions use integers; decimal values are display only.
The script computes an optimal value, not a list of actual forbidden words.
"""
from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext


def certify(a: int, b: int, d: int, max_depth: int, gap_denominator: int) -> dict:
    if not (d >= 3 and a >= b >= 1 and max_depth >= 1 and gap_denominator >= 1):
        raise ValueError('Require d>=3, a>=b>=1, max_depth>=1, gap_denominator>=1')
    denominator = a + (d - 1) * b
    counts = [1]
    remaining_numerator = 1
    denominator_power = 1
    for depth in range(1, max_depth + 1):
        expanded = [0] * (len(counts) + 1)
        for rare_count, count in enumerate(counts):
            expanded[rare_count] += count
            expanded[rare_count + 1] += (d - 1) * count
        removed_rare_count = next(i for i, count in enumerate(expanded) if count)
        expanded[removed_rare_count] -= 1
        counts = expanded
        removed_numerator = a ** (depth - removed_rare_count) * b ** removed_rare_count
        remaining_numerator = denominator * remaining_numerator - removed_numerator
        denominator_power *= denominator
        # gap >= remainder_N - (a/D)^(N+1)/(1-a/D).
        certificate_numerator = ((denominator - a) * remaining_numerator
                                 - a ** (depth + 1))
        certificate_denominator = (denominator - a) * denominator_power
        if certificate_numerator * gap_denominator > certificate_denominator:
            with localcontext() as context:
                context.prec = 40
                remainder = str(Decimal(remaining_numerator) / Decimal(denominator_power))
                tail = str(Decimal(a ** (depth + 1)) / Decimal(certificate_denominator))
                certified_bound = str(Decimal(certificate_numerator)
                                      / Decimal(certificate_denominator))
            return {
                'a': a, 'b': b, 'd': d, 'D': denominator,
                'horizon': depth,
                'last_removed_rare_count': removed_rare_count,
                'finite_survivor_decimal': remainder,
                'universal_tail_decimal': tail,
                'survivor_lower_bound_decimal': certified_bound,
                'strict_gap_certificate': f'> 1/{gap_denominator}',
                'exact_integer_certificate_passed': True,
                'entropy_strictly_below_log2_exact': (
                    denominator ** denominator
                    < 2 ** denominator * a ** a * b ** ((d - 1) * b)),
            }
    return {'a': a, 'b': b, 'd': d, 'D': denominator,
            'tested_through': max_depth,
            'strict_gap_certificate': f'not certified above 1/{gap_denominator}',
            'interpretation': 'inconclusive at this finite horizon; not a zero-gap result'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--a', type=int)
    parser.add_argument('--b', type=int, default=1)
    parser.add_argument('--d', type=int, default=3)
    parser.add_argument('--max-depth', type=int, default=3000)
    parser.add_argument('--gap-denominator', type=int, default=10_000_000)
    args = parser.parse_args()
    cases = [(8, 1, 3, 22, 1000), (18, 1, 3, 73, 10000),
             (98, 1, 3, 729, 10_000_000)] if args.a is None else [
                 (args.a, args.b, args.d, args.max_depth, args.gap_denominator)]
    for case in cases:
        print(json.dumps(certify(*case), ensure_ascii=False, sort_keys=True))


if __name__ == '__main__':
    main()
```

不带参数运行即可得到上述三个实例：

```sh
python3 iid-sparse-prefix-gap-experiment.py
```

程序逐层计算整数计数和 $R_n$，在首次满足严格证书时返回该深度、有限幸存量、尾界、余量下界及整数低熵判断；十进制转化只发生在证书通过之后。它只计算最优值和证书，不输出具体禁词族。无限全族结论由有限交换定理和一致尾界承担，并不是对无限族的程序穷举。若某有限窗口没有取得证书，结论只是该窗口未认证所请求的下界，不能推出 $\eta=0$。证毕。

### 5.5 局部间隔、五个概率接口与移位预算

**定理 5.5.1（原始公告的全局及局部余量）。** 固定 $d\ge3$ 及第 5.1 节的同一正 iid 律。允许原始禁词库存 $\mathcal P$ 重复公告同一词，也允许包含已有禁祖先的冗余后代；要求最终每个正长度至多一个不同词，且不含空词。令
$$
U=\bigcup_{w\in\mathcal P}[w],\quad E=X\setminus U,\quad
M=\mu_p(E),\quad m_v=\mu_p(E\cap[v]).
$$
则 $M\ge\eta(p)>0$，而每个有限词 $v$ 满足完整二分
$$
\begin{cases}
E\cap[v]=\varnothing,\quad m_v=0,
&\text{若存在最终禁词 }w\preceq v,\\
m_v\ge\eta(p)p(v)>0,
&\text{若不存在这样的最终禁词。}
\end{cases}
$$
前缀关系包括等号。根对应空词，因根公告被禁止而总属于第二分支。

**证明。** 在集合论上，保留 $\mathcal P$ 中没有更短 $\mathcal P$ 祖先的词，得到前缀自由族；每个原始词的有限祖先链有一个最短已禁祖先，所以柱并不变，预算也继承。这里没有断言这个最终最小族可有效枚举。第 2.6.3 节已经区分最终规范形和可枚举规范形。

对于实际计算，只需对每个有限公告集去重复、删除有已见更短禁祖先的词。此有限操作有效、柱并不变，并得到 $\mathcal C_1$ 中的族，故其删除质量至多 $B(p)$。有限公告并递增到 $U$，由测度从下连续知 $M\ge1-B(p)=\eta(p)$。

若有 $w\preceq v$，整个 $[v]$ 都被删除。若无此祖先，与 $[v]$ 相交的禁词只能唯一写成 $vu$，其中 $|u|\ge1$。去掉公共前缀 $v$ 后，绝对深度 $|v|+n$ 的一词预算变为相对正深度 $n$ 的一词预算。由于是同一 iid 律，条件尾仍按 $p$ 分布；对每个有限尾库存压缩并应用根处的删除界，再取递增极限，尾幸存质量至少 $\eta(p)$。乘以 $p(v)>0$ 即得局部下界。证毕。

因此 $R(v):=\mathbf1_{\{E\cap[v]\ne\varnothing\}}$ 在语义上等价于没有最终禁祖先，但有限阶段尚未见祖先不是这项否定的证书。令 $\nu=\mu_p(\,\cdot\cap E)/M$，则每个与 $E$ 相交的标准柱都有正 $\nu$ 质量；柱构成拓扑基，故 $E\subseteq\operatorname{supp}\nu$。闭的 $E$ 承载全部概率，又给反向包含，所以 $E=\operatorname{supp}\nu$。这排除的是非空零质量柱切片，并没有把每个无限点变成正质量原子。

**定理 5.5.2（一次质量访问的 iid 延拓算法）。** 再供应正可计算坐标名、完整 c.e. 公告呈示及同一 $M$ 的 Cauchy 名。它们可以全部相对于一个共同 oracle。由这些输入可统一计算所有 $R(v)$；以下每个合法查询只读取一次总质量名。

**参数、定位与精度。** 用定理 5.3.1 或 5.3.2 得有理 $0<\gamma<\eta(p)$，并由正坐标名搜索 $0<\ell_a<p_a$。对词 $v$ 置
$$
g_v=\gamma\prod_{i<|v|}\ell_{v_i}>0.
$$
空积为一。定理 5.5.1 保证切片为空时质量零，非空时 $m_v\ge\eta(p)p(v)>g_v$；根也具有这个严格号。

把公告程序运行前 $s$ 个计算步骤，令 $E_s$ 为已公告有限柱并的补集。每个阶段都能结束，包括没有新公告的阶段；它们统一为有效 clopen 集，且 $E_s\downarrow E$。置
$$
f_s=\mu_p(E_s)\downarrow M,\qquad
u_s=\mu_p(E_s\cap[v])\downarrow m_v.
$$
有限柱积、有限并和交的质量由同一 $p$ 名统一可计算，一般为实数而非有理数。取 $g=g_v$，选整数 $t$ 使 $2^{-t}\le g/16$，只读取这一次 $v_M(t)$，并固定
$$
L=v_M(t)-2^{-t},\qquad 0\le M-L\le2^{1-t}\le g/8.
$$
引理 4.3.4 以 $K_s=E_s$、$K=E$、$C=[v]$、$\mu=\mu_p$ 代入，正好给
$$
\max\{0,L-(f_s-u_s)\}\le m_v\le u_s,
\qquad
u_s-\max\{0,L-(f_s-u_s)\}\le f_s-L.
$$
其中 $f_s-u_s$ 是同一个概率空间内 $E_s\setminus[v]$ 的质量；该分割正是第 2.3.3 节及第 2.7.2 节式（TM.570）—（TM.571）的局部化合同，未用另一个对象的总质量充当本对象下界。

逐个阶段以误差小于 $g/48$ 近似 $f_s$，再加 $g/48$，形成有理上界
$$
f_s\le F_s<f_s+g/24.
$$
搜索有理条件 $F_s-L<g/3$；失败便进入下一阶段。由于
$$
F_s-L<f_s-M+g/24+g/8=f_s-M+g/6,
$$
且 $f_s\downarrow M$，这个搜索必终止。成功时区间宽度小于 $g/3$；再取有理 $u$，使 $|u-u_s|<g/12$。空切片时 $u_s<g/3$，所以 $u<5g/12$；非空时 $u_s\ge m_v>g$，所以 $u>11g/12$。于是
$$
R(v)=1\quad\Longleftrightarrow\quad u>g/2.
$$
等号不会发生。这是定理 4.3.5 的具体 iid 代入，保留其全部实数误差余量。非法词直接返回零；根既可直接返回一，也可按上述空积算法处理。质量名若脱离同一呈示，单独不包含禁柱位置；本算法明确保留呈示输入。证毕。

**命题 5.5.3（真实外部体积与两个反向算法）。** 以最终真实延拓定义
$$
R_n=\{v\in\Sigma^n:R(v)=1\},\quad
A_n=\bigcup_{v\in R_n}[v],\quad
a_n=\mu_p(A_n)=\sum_{v\in R_n}p(v).
$$
则
$$
E\subseteq A_n,\qquad
A_n\setminus E\subseteq\bigcup_{\substack{w\in\mathcal P\\|w|>n}}[w],
\qquad 0\le a_n-M\le\frac{m^{n+1}}{1-m}.
$$
给参考概率名和 $R$，不需库存枚举即可计算 $M$。给参考概率名及条件柱概率接口 $\mathbf C$，也可计算 $M$，并且不查询 $R$。

**证明及实现。** 命题 4.3.6 已有第一组包含：若 $x\in A_n\setminus E$，其深度 $n$ 柱中存在一个最终幸存者；任何删掉 $x$ 的禁词若长不超过 $n$，就会同时删掉该幸存者。因此只能是更深禁词，再用每正深度至多一词及 $p(w)\le m^{|w|}$ 求尾和。本方向只需要真实延拓必无禁祖先，不使用定理 5.5.1 的充分方向。

有效地搜索 $m<r<1$ 后，取 $n$ 使 $r^{n+1}/(1-r)<2^{-k-1}$，查询全部 $d^n$ 个 $R(v)$，将实际加权和 $a_n$ 近似至误差小于 $2^{-k-1}$。两项相加给 $2^{-k}$ 的质量名。所需信息是参考律、预算及 $R$，不需要再运行禁词程序；不能用 $|R_n|/d^n$ 替代实际非均匀加权和。

条件律方向取第 4.1 节的完整分割 $\mathcal D_n=\{[v]:v\in\Sigma^n\}$，权重 $w_{n,v}=p(v)>0$，以及刚证明的有效外部体积误差。其全部单元有有效 clopen 描述，参考柱和条件柱的名字均可用，故命题 4.1.2 给
$$
D_n=\max_{v\in\Sigma^n}\frac{\nu([v])}{p(v)},\qquad
1\le D_n\le M^{-1},\qquad
M\le D_n^{-1}\le a_n\le M+\frac{r^{n+1}}{1-r}.
$$
算法取尾小于 $2^{-k-2}$ 的层，将全部密度比算到误差至多 $2^{-k-2}$ 后取最大近似 $d_n$，截为 $\widetilde D_n=\max(1,d_n)$，输出 $1/\widetilde D_n$。定理 4.1.4 的正分母下界搜索及倒数 Lipschitz 界给总误差小于 $2^{-k}$。它遍历完整层，并不先询问哪些柱可延拓；$R_n,A_n$ 只在证明中出现。证毕。

**定理 5.5.4（同一模型上的五接口等价）。** 给有限 $d\ge3$、正可计算 $p$ 和定理 5.5.1 的完整可枚举库存，采用定理 5.5.2 的同一阶段序列。相对于任意共同 oracle $A$，定义 4.2.1 的五个接口在这里均匀互算：
$$
\mathbf M\ \longleftrightarrow\ \mathbf C\ \longleftrightarrow
\mathbf T\ \longleftrightarrow\ \mathbf S\ \longleftrightarrow\ \mathbf R.
$$
这些符号具体是同一 $M$ 的有理 Cauchy 名、同一 $\nu=\mu_p(\,\cdot\cap E)/M$ 的全部条件柱名、指定 $\nu_s=\mu_p(\,\cdot\cap E_s)/f_s$ 的总变差阶段选择器、公平位精确在线采样器，以及同一 $E$ 的真实延拓特征函数。

**证明与合同。** 定理 5.5.1 给 $M\ge\eta(p)>0$，所以每个 $f_s\ge M$ 严格正。常数字母表及全部有限层可有效列出，参考柱质量为可计算乘积，$E_s$ 为统一可计算递减 clopen 呈示，故定理 4.2.3–4.2.5 的全部条件都满足。它们给
$$
\mathbf M\longleftrightarrow\mathbf T\longrightarrow\mathbf C
\longleftrightarrow\mathbf S.
$$
命题 5.5.3 的最大密度算法供应 $\mathbf C\to\mathbf M$，其加权外部体积算法供应 $\mathbf R\to\mathbf M$，定理 5.5.2 供应 $\mathbf M\to\mathbf R$，闭合五接口。

这里总变差采用 $\sup_{B\text{ Borel}}|\nu_s(B)-\nu(B)|$，由命题 4.2.2 恰等于 $(f_s-M)/f_s$。$\mathbf T$ 是全函数 $g$，满足 $d_{\mathrm{TV}}(\nu_{g(k)},\nu)\le2^{-k}$，必须针对所指定的这份阶段序列。$\mathbf M\to\mathbf T$ 沿用定理 4.2.3 的正下界及严格比较交错搜索，不能在一个早期不合格实阶段无限等待；$\mathbf T\to\mathbf M,\mathbf C$ 对一般实阶段把阶段误差和数值误差各分一半。没有把定性阶段收敛当作已经供应有效阶段。

$\mathbf S$ 使用公平 iid 随机位，每次输出只读有限输入，输出不可撤回，几乎必然无限生产且其 Borel 律精确等于 $\nu$。定理 4.2.4 的相容区间细分及可数零测端点处理负责 $\mathbf C\to\mathbf S$；定理 4.2.5 的有效开输出事件、同层有限互斥及总质量一负责反向转换，不需要输出等待模量。若机器可正概率停止，只得到第 2.10.9 节的半测度合同，不能先条件化无限成功再把它报为 $\mathbf S$。也没有把某个支撑相同的任意概率律换作这里指定的 $\nu$。

还有一条定性的 $\mathbf C\to\mathbf R$ 路线：定理 5.5.1 给 $E=\operatorname{supp}\nu$，可按命题 4.3.3 并行搜索 $\nu([v])>0$ 与 $E_s\cap[v]=\varnothing$。非空时前者终止；最终为空时，紧致性使递减紧集不可能全非空，故某有限阶段已空，后者终止。它使用同一有效闭呈示，不能仅凭一般支撑正信息就省去负分支；也不提供定理 5.5.2 的固定概率精度预算。证毕。

五接口的机器转换均在所列语义承诺域上工作，不判定任意输入是否满足预算。给出的名字可能携带额外信息，结论是固定输入和任意共同 oracle 下的可计算性等价，不是每个任意名字的精确 Turing 度等式。实数精度、名字位长、$d^n$ 层枚举、公告等待及公平采样读取是不同成本；没有给统一运行时或一般期望等待界。由 $R$ 从根逐层选择首个可延拓孩子可得一个幸存点，反向从一个点求全部 $R$ 则没有这样的结论。

**命题 5.5.5（一般预算的逐查询移位条件）。** 对一般次指数预算 $b$，原始库存仍按最终不同词计费，允许重复和冗余。固定一个查询词 $v$，令 $h=|v|$、
$$
b^{[h]}_n=b_{h+n}\quad(n\ge1).
$$
如果另有该查询的严格预算承诺
$$
\sum_{n\ge1}b_{h+n}d^{-n}<1,
$$
则在没有最终禁祖先时
$$
\mu_p(E\cap[v])\ge p(v)\eta_{b^{[h]}}(p)>0;
$$
有禁祖先时仍为空。全局条件 $B_d(b)<1$ 不能代替这里的移位条件。

**证明及有效适配。** 无祖先时，所有相交禁词都是 $vu$，去掉共同前缀得到相对深度预算 $b_{h+n}$，尾律仍是 $p$。固定移位保持次指数性：给 $a>1$，选 $1<t<a$，使充分大 $n$ 有 $b_{h+n}\le t^{h+n}\le a^n$。因此对有限尾公告作前缀压缩、应用定理 5.2.2 的移位预算版本并取递增极限，就得到所示下界。这里具体消耗了移位均匀和严格小于一；只知道根处预算和不足以进行这个代入。

若供应有效次指数模量 $\nu_{\mathrm{bud}}$，即对有理 $t>1$ 给一个整数阈值使 $b_j\le t^j$ 对全部 $j\ge\nu_{\mathrm{bud}}(t)$ 成立，则对有理 $a>1$，选择有理 $1<t<a$，搜索整数 $N_1$ 使
$$
(a/t)^{N_1}\ge t^h,
\qquad
\nu_h(a)=\max\{1,\nu_{\mathrm{bud}}(t),N_1\}.
$$
因 $a/t>1$，有理幂搜索终止。对 $n\ge\nu_h(a)$，有 $n+h\ge\nu_{\mathrm{bud}}(t)$，且 $(a/t)^n\ge t^h$，故
$$
b^{[h]}_n=b_{n+h}\le t^{n+h}\le a^n.
$$
这正是移位有效模量。也可以直接供应每个所需移位的有效尾界；仅有模量存在的语义承诺，不能自动提取这份数据。

给可计算 $b,p$、本查询的严格移位预算承诺及这份有效模量，定理 5.6.1 的预算算法输出有理 $0<\gamma_h\le\eta_{b^{[h]}}(p)$。配合正坐标下界，取
$$
g_v=\frac{\gamma_h}{2}\prod_{i<|v|}\ell_{v_i}.
$$
这保证非空切片严格大于 $g_v$，包括 $h=0$ 的空积；所以定理 4.3.5 的全部一次查询常数再次适用。每次查询使用其实际 $h$ 和所供应的对应承诺与模量，不把某一柱的证书当作全部柱的证书。

若要从总质量统一输出全部 $R$，必须对每个查询统一履行上述移位承诺和有效尾供应，并保留同一参考律及呈示。若还满足根处 $B_d(b)<1$ 并供应其有效尾，则 $M\ge\eta_b(p)>0$，且有一般版本的 $0\le a_n-M\le\sum_{j>n}b_jm^j$，从而接入第 4.1–4.2 节的四概率接口和 $\mathbf R\to\mathbf M$；加入全体查询的局部供应才有五接口。单个移位承诺只给该柱的决定，不等于已经提供一个全域 $\mathbf R$ 接口。证毕。

### 5.6 有效预算供应与非统一可计算性的区别

**定理 5.6.1（给定有效尾的预算最优值算法）。** 给有限 $d\ge2$、可计算正概率 $p$、可计算非负整数预算 $b$，以及有效次指数模量 $\nu_{\mathrm{bud}}$。这些程序和名字允许相对于同一 oracle。则最优删除质量 $M_b(p)$ 可统一计算；若另承诺 $B_d(b)<1$，可统一输出一个正有理下界 $0<\gamma_b\le\eta_b(p)$。

**证明及算法。** 如定理 5.3.1，从坐标名严格搜索 $m_p<r<1$，再选有理 $1<a<1/r$。取
$$
N_0=\nu_{\mathrm{bud}}(a),\qquad
T_N=\frac{(ar)^{N+1}}{1-ar}\quad(N\ge N_0).
$$
这里实际只消费所选这一个 $a$ 的最终界；若直接给这一 $a,N_0$ 及其承诺，也足够，不必取得完整模量的其他值。

对每个有限 $N$，计算 $b_1,\ldots,b_N$，枚举所有 $S_n\subseteq\Sigma^n$、$|S_n|\le b_n$，并检查全部跨层前缀条件。空集选择保证可行候选非空。设这些有限族的最大删除质量为 $M_N^{\mathrm{del}}$；和定理 5.3.1 一样，可计算有限最大值而无需决定精确并列。用全空后续层延长和截断无限族，分别得到
$$
M_N^{\mathrm{del}}\le M_b(p)\le M_N^{\mathrm{del}}+T_N
\qquad(N\ge N_0).
$$
选择使 $T_N$ 足够小的 $N$，并按请求精度近似有限最大值，就得到 $M_b(p)$ 的 Cauchy 名。此处 $M_b$ 和 $M_N^{\mathrm{del}}$ 是删除优化值，与第 5.5 节某个具体库存的幸存质量 $M$、以及命题 5.4.2 的有限幸存量 $M_N^{\mathrm{fin}}$ 不同。

在严格预算承诺下，定理 5.2.2 给 $M_b(p)<1$。依次考察 $N\ge\max(1,N_0)$，计算有理上近似
$$
M_N^{\mathrm{del}}\le U_N\le M_N^{\mathrm{del}}+2^{-N}.
$$
例如将有限最大值算到误差至多 $2^{-N-1}$ 后加 $2^{-N-1}$。检验有理条件 $U_N+T_N<1$，成功时输出
$$
\gamma_b=1-U_N-T_N>0.
$$
因为 $M_b\le U_N+T_N$，所得数至多 $1-M_b=\eta_b$。又 $M_N^{\mathrm{del}}\to M_b$、$T_N\to0$、$2^{-N}\to0$，严格的 $M_b<1$ 保证搜索终止。算法不必预先计算 $B_d(b)$ 的精确和或其与一的距离；但正确性和终止确实使用其严格承诺，不能自行免除。

对于已知常数预算 $b_n\le c$，可直接用
$$
T_N=\frac{c r^{N+1}}{1-r}
$$
而无需一般模量。特别常数预算 $b_n=c$ 在 $d\ge c+2$ 时，推论 5.2.3 供应正余量搜索的终止；$c=0$ 时最优删除为零、余量为一。这里“已知 $c$”是输入数据，不等于只承诺存在某个有限界。证毕。

**定理 5.6.2（不供应有效尾时不能统一提取正余量）。** 即使实际概率固定为可计算均匀律，仅给可计算预算的程序，并承诺它次指数且 $B_d(b)<1$，也不存在总在该承诺域终止的统一算法，输出正有理数 $r_b\le\eta_b(p)$。在相同输入合同下，也不能统一计算 $M_b(p)$。

**证明。** 固定任意 $d\ge2$ 及 $p=(1/d,\ldots,1/d)$。令 $U_e(0)$ 是第 $e$ 个程序在固定输入零上的计算；任意程序输入对可以有效编译为这样的固定输入程序，所以此停机集合仍不可判定。令 $T(e)$ 为使计算在前 $n-1$ 次转移内已经停机的最小整数 $n\ge1$，若永不停机则未定义。初始状态已经停机时 $T(e)=1$；$T(e)=n$ 可由有限模拟判断。

统一定义预算程序
$$
b_n^e=
\begin{cases}
d^n-1,&T(e)=n,\\
0,&\text{否则}.
\end{cases}
$$
这对 $(e,n)$ 可计算，每个实例至多一个非零项，因而有限支撑、次指数。全部输入都满足严格预算承诺：若不停止，$B_d(b^e)=0$；若 $T(e)=n$，则 $B_d(b^e)=1-d^{-n}<1$。

不停止时唯一合法族为空，最优删除质量为零。若停在 $n$，合法族只能使用第 $n$ 层，任取该层 $d^n-1$ 个词均前缀自由，每词均匀质量 $d^{-n}$，恰好取得预算上界。因此
$$
M_{b^e}(p)=
\begin{cases}
0,&T(e)\text{ 未定义},\\
1-d^{-n},&T(e)=n,
\end{cases}
\qquad
\eta_{b^e}(p)=
\begin{cases}
1,&T(e)\text{ 未定义},\\
d^{-n},&T(e)=n.
\end{cases}
$$
假设存在所述算法。给每个预算程序 $b^e$，它都必须终止并输出 $0<r_e\le\eta_{b^e}(p)$。搜索 $N\ge1$ 使 $d^{-N}<r_e$，再模拟到阶段 $N$，即包括初始状态及前 $N-1$ 次转移。若已经停止就回答停机；若尚未停止，任何未来停止阶段 $n>N$ 都将给
$$
r_e\le d^{-n}<d^{-N}<r_e,
$$
矛盾。因此尚未停止时可回答永不停止，得到停机判定器，矛盾。

若能在相同输入上统一计算 $M_{b^e}(p)$，因全部实例都满足 $1-M_{b^e}(p)>0$，从其名字搜索正有理下界便给上面已排除的算法。因此统一最优值计算也不可能。反例没有固定一个非可计算预算：每个预算都可计算且有限支撑，只是没有给出可统一获得的支撑终点或有效尾模量。它们逐个也都有某个有限常数上界，故无数值供应的“预算有界”承诺同样不够。证毕。

**命题 5.6.3（逐实例计算与单向逼近）。** 对每个固定可计算次指数预算 $b$ 和固定可计算正 $p$，最优删除质量 $M_b(p)$ 是可计算实数，尽管从任意这些程序统一提取它不成立。若 $B_d(b)<1$，其补 $\eta_b(p)$ 也是严格正的可计算实数。另一方面，仅给 $b,p$ 的程序时，仍能统一下半计算 $M_b(p)$、上半计算 $\eta_b(p)$。

**证明。** 对固定 $p$，搜索某个 $m_p<r<1$ 并选择有理 $1<a<1/r$。次指数性保证存在一个适用于这个 $a$ 的有限整数 $N_0$。把实际合格的 $N_0$ 写成程序常量，定理 5.6.1 的有限优化及几何尾算法就计算该固定 $M_b$。这是存在一个带有限常量的计算程序，不是从任意预算程序取得正确常量的统一过程；不与定理 5.6.2 矛盾。严格正性再由定理 5.2.2 给出。

不供应 $N_0$ 时，仍可枚举全部有限可行族，对每个质量值不断计算有理下界，交错处理所有族并取截至当前的最大下界，得到递增的有效下近似。每个无限合法族的非负和是其有限截断和的上确界，所以这些下近似的极限恰为 $M_b$；从一减去它们给 $\eta_b$ 的递减上近似。这份单向信息，即使加上严格正余量承诺，也不能统一产出正下界，定理 5.6.2 已以实际停机归约证明该边界。证毕。

### 5.7 锐的端点与全局余量不能保证局部支撑的反例

**命题 5.7.1（二元梳与非空零质量柱）。** 对任意严格正二元 iid 概率 $p_0+p_1=1$，一词预算存在满质量族
$$
\mathcal F=\{0^n1:n\ge0\},\qquad
S_{\mathcal F}(p)=\sum_{n\ge0}p_0^np_1=1.
$$
其幸存集为 $\{0^\infty\}$，质量为零，故 $B(p)=1$、$\eta(p)=0$。若只取 $n\ge1$，则
$$
E=[1]\cup\{0^\infty\},\qquad M=p_1>0,\qquad
E\cap[0]=\{0^\infty\},\qquad\mu_p(E\cap[0])=0.
$$

**证明。** 每个有字母一的路径有唯一的首次一，其位置决定唯一禁词；不同这样的禁词在较短词的末位已经不同，故前缀自由，每正深度恰好一词。全部未被删除者只有全零路径，单点质量为 $\lim_n p_0^n=0$。去掉 $n=0$ 的词就是不禁首位一，余下仍删掉每个首位零且以后出现一的路径，得到第二组等式。证毕。

第二个对象正是命题 4.7.7 的二元家族在没有追加禁词 $0$ 时的形状；那里加入停机控制后，四个概率输入相同而跨呈示延拓不能统一恢复。此处没有把正总质量等同于每个局部切片正质量。第一对象的 $M=0$ 也不能被当作已定义归一化条件律的五接口实例。

**命题 5.7.2（正概率向边界逼近时没有共同数值余量）。** 固定 $0<a<1$，对 $0<\epsilon<1$ 取三元向量
$$
p^{(\epsilon)}=(a(1-\epsilon),(1-a)(1-\epsilon),\epsilon).
$$
全部三个坐标都严格正。同一梳族 $\{0^n1:n\ge0\}$ 的幸存质量恰为
$$
1-\frac{(1-a)(1-\epsilon)}{1-a(1-\epsilon)}
=\frac{\epsilon}{1-a+a\epsilon}\longrightarrow0
\quad(\epsilon\downarrow0).
$$
因此每个固定正 $p$ 的 $\eta(p)>0$，不意味着存在适用于全部正三元律的统一正常数。

**证明。** 该族仍前缀自由且每正深度一词，只是含第三字母的路径另有幸存可能。删除质量按同一 iid 律为 $p_1/(1-p_0)$，代入并化简得到公式。$\eta(p^{(\epsilon)})$ 不超过这个具体族的幸存质量，所以任意声称的共同正下界都被充分小的 $\epsilon$ 排除。参数统一算法允许其输出依赖实际坐标，并不与这个反例冲突。证毕。

**定理 5.7.3（常数预算的精确阈值）。** 对整数 $c\ge0$、实际有限字母数 $d\ge2$，每个固定全正 iid 律下、全部每层至多 $c$ 词的前缀自由无根族具有共同正幸存余量，当且仅当 $d\ge c+2$。$c=0$ 时余量恰为一；$c\ge1$ 时，即使位于正余量区域，也没有适用于全部正 $p$ 的共同正数值常数。

**证明。** 正方向已由推论 5.2.3 的 $c/(d-1)<1$ 给出。若 $c\ge d-1$，固定字母 $a\in\Sigma$，取
$$
\mathcal F_a=\{a^{n-1}z:n\ge1,\ z\ne a\}.
$$
每层恰有 $d-1$ 个词。每个词在其最后位置第一次离开字母 $a$，因此不同词互不为前缀，且
$$
S_{\mathcal F_a}(p)=\sum_{n\ge1}p_a^{n-1}\sum_{z\ne a}p_z
=\sum_{n\ge1}p_a^{n-1}(1-p_a)=1.
$$
幸存者仅为 $a^\infty$，其质量为零。整数条件 $d<c+2$ 等价于 $c\ge d-1$，于是两个方向恰好穷尽。$c=1$ 给 $d\ge3$ 与二元端点；在二元中交换字母还能写成另一梳 $\{0,10,110,\ldots\}$。$c=0$ 只允许空族，余量为一。最后，$c\ge1$ 时单词族 $\{a\}$ 合法，余量至多 $1-p_a$；保持其他坐标严格正而令 $p_a\uparrow1$，便排除对所有 $p$ 的共同正下界。证毕。

**命题 5.7.4（显式有界预算的局部零质量反例）。** 固定 $d\ge2$、正 iid 律和一个长度 $h\ge1$ 的词 $v$，再固定字母 $a$。令
$$
b_j=0\quad(1\le j\le h),\qquad b_{h+n}=d-1\quad(n\ge1),
$$
$$
\mathcal F_v=\{v a^{n-1}z:n\ge1,\ z\ne a\}.
$$
预算显式有界且次指数，满足全局严格条件
$$
B_d(b)=\sum_{n\ge1}(d-1)d^{-(h+n)}=d^{-h}<1.
$$
然而
$$
E=(X\setminus[v])\cup\{va^\infty\},\qquad
M=1-p(v)>0,\qquad
E\cap[v]=\{va^\infty\}\ne\varnothing,
\qquad\mu_p(E\cap[v])=0.
$$
故全族根处正余量不能单独推出本对象的局部正间隔或 $E=\operatorname{supp}\nu$。

**证明。** $\mathcal F_v$ 是定理 5.7.3 的梳加上共同前缀，仍前缀自由，每个使用的绝对深度恰好 $d-1$ 个词，无根也无 $v$ 的禁祖先。它在 $[v]$ 内删掉全部尾部并非全 $a$ 的路径，且不删除柱外的点，故得到所示集合。因为 $p_a<1$，该单点质量为 $p(v)\lim_n p_a^n=0$；又 $h\ge1$ 及每个坐标小于一保证 $p(v)<1$，所以总质量严格正。条件律实际支撑为闭开集 $X\setminus[v]$，不包含那个孤立于支撑的幸存点。

对长度 $h$ 的这次查询，移位预算为恒等的 $d-1$，其均匀和却是
$$
\sum_{n\ge1}b_{h+n}d^{-n}=\sum_{n\ge1}(d-1)d^{-n}=1.
$$
这精确指出命题 5.5.5 不能从根预算直接推下去的一步。全局定理 5.2.2 仍正确；失效的是未履行移位严格条件的局部代入。这里不主张已经给出一般非恒定预算局部恢复的必要充分分类。证毕。

这些端点都保留指定概率及其实际长度预算。它们没有推广到任意非 iid 律、平稳 Parry 初始混合或无限字母；一般预算的正结论仅在第 5.2、5.6 节的受限条件及第 5.5.5 节的逐查询条件中成立。集合可逆换码仍须另外运输概率、合法实验、时钟和预算。这些无限路径结论不判定有限同余覆盖、E7、逻辑独立性或物理规律。

### 5.8 与既有数量化接口的连接及剩余范围

**推论 5.8.1（一词 iid 问题的准确范围）。** 第 4.8.4 节保留的一般正 iid 一词问题，在以下模型中由本章给出精确的字母数分界：实际有限全正字母表、同一 iid 尾律、无根禁词、按实际正词长每层至多一个最终不同词。$d\ge3$ 时每个固定 $p$ 都有全族正余量；再给可计算坐标名和完整有效库存呈示，就有定理 5.5.4 的有效五接口。$d=2$ 时命题 5.7.1 给满质量梳，即使另加具体库存 $M>0$，也有非空零质量柱及命题 4.7.7 的统一性障碍。

**证明与边界。** 存在结论为推论 5.2.3，参数有效性为定理 5.3.1–5.3.2，局部条件及接口为定理 5.5.1–5.5.4；有效结论均保留可计算概率名和完整库存呈示。反向端点由命题 5.7.1 承担。一般预算方面，定理 5.2.2 给次指数且 $B_d(b)<1$ 的充分区域，定理 5.7.3 另外给常数预算的必要充分阈值；本章没有把这两者扩大成任意预算的分类。证毕。

#### 5.8.2 Rényi、Shannon 与 Perron 算法的数量化作用

定理 4.6.2–4.6.4 仍给一套直接可用的数值界。在同一个正有限 iid 向量和一词预算上，对 $q>1$ 置
$$
c_q=\sum_a p_a^q,\qquad r_q=c_q^{1/(q-1)},\qquad
\eta_q=1-\left(\frac{r_q}{1-r_q}\right)^{(q-1)/q}.
$$
若 $r_q<1/2$，则 $\eta(p)\ge\eta_q>0$，原始库存的总幸存质量至少 $\eta_q$，无禁祖先切片质量至少 $\eta_q p(v)$。这些数值结论不需要执行本章的大规模有限优化或坐标运输。其通用证明所有者仍是定理 4.6.2：辅助律 $\widehat p_{q,a}=p_a^q/c_q$ 的前缀柱不交给 $\sum_w\widehat p_q(w)\le1$，一词正长度预算给 $\sum_w r_q^{|w|}\le r_q/(1-r_q)$。以非负可和函数 $f(w)=\widehat p_q(w)$、$g(w)=r_q^{|w|}$ 和正互补指数 $1/q,(q-1)/q$ 调用可数加权 Hölder，逐项乘积正好为 $p(w)$。这明确履行 `countable_weighted_holder_interpolation` 的两项可和性和指数条件；它不是本章开闭传播分类的替代证明。

平方代入 $q=2$ 原样给
$$
c=\sum_a p_a^2,\qquad r_2=c,\qquad
\eta_2=1-\sqrt{\frac c{1-c}}\quad(c<1/2).
$$
其 Cauchy–Schwarz 与有限子集极限证明归推论 4.6.3；辅助概率仅作估计，不替换实际参考律。定理 4.6.5 的 Shannon 路线也保留：有限正坐标使 $H_q(p)\to H(p)$ 当 $q\downarrow1$，严格承诺 $H(p)>\log2$ 保证某个 $q_j=1+1/j$ 合格。第 $m$ 轮同时对全部 $1\le j\le m$ 计算宽度至多 $2^{-m}$ 的 $r_{q_j}$ 包含区间，接受某个上端 $u<1/2$，取
$$
q=q_j,\qquad\rho=(u+1/2)/2,\qquad
0<\gamma<1-\left(\frac\rho{1-\rho}\right)^{(q-1)/q}<\eta_q.
$$
最后的有理 $\gamma$ 由正实数下界搜索取得。固定的合格 $j$ 在充分精度后被认证，保证交错搜索终止；不能固定一个不合格 $j$ 等待，也不要求预给熵差的数值下界。各字母的 $\ell_a<p_a$ 再给 $g_v=\gamma\prod_i\ell_{v_i}$，交给定理 4.3.5 或第 5.5.2 节的同一误差算法。命题 4.6.7 的 $H_q\le H$ 与趋一极限是不同结果；阶二的仓内熵比较没有被冒作一般阶证明。

命题 5.4.3 的三个 $H(p)<\log2$ 实例都有严格余量，故 Shannon 门槛不是本章全族正余量的必要条件。由 $H_q\le H$，这些例子也不靠某个 $q>1$ 的 $r_q<1/2$ 门槛通过。这个扩展并不抹去旧估计的显式数值价值，亦不把未结束的熵搜索或失败的有限整数窗口报为零余量。

对 Perron 回返模型，固定第 4.7.1 节的根 $\lambda_k$ 和块律
$$
\sum_{r=0}^{k-1}\lambda_k^{-r-1}=1,\qquad
p_r=\lambda_k^{-r-1},\qquad
p(v)=\lambda_k^{-L(v)},\quad L(v)=\sum_{i<|v|}(v_i+1).
$$
取 $d=k$ 即履行本章的有限正 iid 条件。对 $k\ge3$，第 4.7.3–4.7.4 节已有更直接的特定数值供应
$$
c_k=\frac{3-\lambda_k}{1+\lambda_k},\qquad
\eta_k=1-\sqrt{\frac{3-\lambda_k}{2(\lambda_k-1)}}>\frac16.
$$
因此 $\eta(p)\ge\eta_k>1/6$；无禁祖先柱的局部质量大于 $p(v)/6$。本章没有宣称已找到比这个数值更好的统一 Perron 常数。

定理 4.7.5 的原八分之一算法仍可完整使用：令
$$
g=2^{-L(v)-3},\qquad t=L(v)+7,
$$
或只用块深度 $h$ 时取 $g=2^{-kh-3},\ t=kh+7$。因为 $p(v)\ge2^{-L(v)}$ 及局部幸存比例严格大于 $1/8$，有 $m_v=0$ 或 $m_v>g$，且 $2^{-t}=g/16$。一次质量查询固定 $L_M=v_M(t)-2^{-t}$ 后，仍用 $g/48$ 的阶段近似、$g/24$ 的有理上误差、$F_s-L_M<g/3$ 的停止条件和 $g/12$ 的局部近似；两分支分别低于 $5g/12$、高于 $11g/12$，阈值是 $g/2$。第 4.7.4 节的六分之一加强没有改变这份精度或资源合同。

反向仍可按定理 4.7.6，选 $n$ 使
$$
\frac{(5/9)^{n+1}}{1-5/9}<2^{-m-1},
$$
查询全部 $k^n$ 个真实延拓，将 $\sum_{v\in R_n}\lambda_k^{-L(v)}$ 近似到误差小于 $2^{-m-1}$。其原有 $\lambda_k>9/5$ 保证尾界有效；这个方向不需库存枚举。精度 $L(v)+7$ 和层查询数 $k^n$ 各自保留意义，都不是对枚举、根计算、实数运算或采样的总运行时间承诺。$k=2$ 时沿用第 4.7.7–4.7.8 节的二元反例；根律不换成平稳 Parry 初始律。

#### 5.8.3 优化、实际库存与表示运输

$B(p)$ 或 $M_b(p)$ 是对所有可行族的最优删除质量，它们的有限截断由已知有限选择空间枚举取得。具体 c.e. 库存的 $M=\mu_p(E)$ 则取决于哪些词最终公告；即使已知深词总质量很小，也不能知道某个未见短词是否会出现。定理 5.3.1 和 5.6.1 计算的是前一种优化值，并没有免费计算任意后一种 $M$。第 2.2 节的同一三进对角呈示满足一词预算及正均匀 iid 律，却有第 2.4.8、2.7.5 节所证的不可计算质量，是这个区别的现成实例。

一般预算中，数学存在、每个固定实例的可计算性、从程序统一提取是三个量词：定理 5.2.2、5.6.3、5.6.1 分别给相应的正结论，定理 5.6.2 指出最后一项为何需要有效尾数据。全局根余量与逐柱局部余量也是不同供应；命题 5.7.4 的反例和命题 5.5.5 的移位修复明确了这一接口。坐标下界算法仍限于 $d\ge3$；最终最小禁族只作集合论对象，计算中只使用有限阶段压缩，没有新增最终规范族可枚举或最终无祖先可判的断言。

本章向概率接口代入的实际所有者为第 4.1 节的正权有限分割和有效外部体积、第 4.2 节的同一有效闭呈示与公平采样、第 4.3 节的局部间隔和实阶段定位；更早的第 2.9 节拥有等权变量进制几何，第 2.10.4、2.10.6、2.10.8、2.10.9 节分别拥有条件化、总变差、持续输出和停止流。一般质量局部化归第 2.3.3 节，单柱精度形式归第 2.7.2 节，不重复建立一个独立通用所有者。第 4.4–4.5 节的点态与统一性反例、有效观察精度与总变差精度区别，均保留其原模型及结论。

原生编码运输仍使用第 1.4.2–1.4.4 节和第 4.7.9–4.7.11 节：完整回返块加未完成 run 给全部有限窗口，原始时钟为块屋顶长度之和，原始一步是块内倒计时或跨块移动。预算不能仅由同胚或词数运输；$[0],[10],\ldots,[1^{k-1}0]$ 在不同原始深度各出现一次，却在块深度一覆盖全部块字母。反向也有块词 $(1),(0,0)$ 展开后同长为二的例子。第 1.3.6 节消费的是 A 卷第 2.17 节的加权继续任务：共同测试集、双向合法性、保持拼接的统一测试双射、转移交织、终端观察和可消去交换幺半群中的可加成本及原始时长，缺项时不能仅凭数值编码双射取得相同继续商。

#### 5.8.4 数学来源与未覆盖的范围

开闭传播、紧致取得、参数算法和贪心交换在本章分别给出完整证明；它们使用有限柱概率、多项式连续性、几何尾、连通性和紧致性等标准工具。一般次指数证明是第 5.2 节的所有者，一词情形保留跳层空间、$C(q,p)m$ 的具体常数及 $1/(d-1)$ 的均匀上界；第 5.3–5.4 节再处理它独有的坐标算法和交换算法。一般证明的复用不替代这些具体参数、分支和计算证书。

Rényi 倾斜与平方特例的证明分别归定理 4.6.2、推论 4.6.3，共同 iid 尾下的局部余量归定理 4.6.4，Shannon 极限及有效参数搜索归定理 4.6.5，一般阶熵比较归命题 4.6.7。它们保留定义 4.6.1 的有限全正字母、无根和每正词长至多一词条件；局部余量与参数搜索分别使用所列严格倾斜门槛和严格 Shannon 门槛，辅助倾斜律只用于估计。

Perron 回返根及实际块权归定义 4.7.1；平方和、八分之一间隔及六分之一加强归命题 4.7.3、推论 4.7.4；保留原精度的单次质量查询和加权反向算法归定理 4.7.5–4.7.6。这些数量化间隔和算法限于至少三个块字母，并保留同一固定回返初态律和正块深度预算；正向查询需要完整有效库存呈示，反向算法不需库存枚举。二元边界及原始窗口、时钟、预算运输分别归第 4.7.7–4.7.8、4.7.9–4.7.11 节。回返根律与平稳初始律的区分及 W. Parry 的文献归属沿用第 4.8.2 节。

加权外部体积、最大密度夹逼及实权重质量恢复归定义 4.1.1、命题 4.1.2 和定理 4.1.4，使用完整有限分割、严格正实际权重及有效外部体积误差。总质量、条件律、总变差阶段与公平采样的转换归第 4.2 节，保留正总质量、同一参考律、同一有效闭呈示、共同 oracle、指定阶段序列，以及公平位、不可撤回输出和几乎必然无限生产。真实外并的尾包含归命题 4.3.6，一般实阶段的局部化及一次查询误差归引理 4.3.4、定理 4.3.5；从质量判非空仍需严格局部间隔，或命题 4.3.3 的支撑等号及双搜索。概率律与公平采样沿用第 4.8.1 节对 Ackerman–Freer–Roy 及其所引 Galatolo–Hoyrup–Rojas、Hoyrup–Rojas 的归属，支撑正信息归 Pauly–Fouché；负判定仍由同一有效闭呈示和紧致性承担。

仓内数学来源的范围依第 4.8.2–4.8.3 节：`countable_weighted_holder_interpolation` 接受已证非负可和函数和正互补指数；两条有限二元 Kraft 声明不自动给非均匀可数前缀界；`collision_entropy_le_shannon_entropy` 只给有限归一化向量的阶二比较。`markov_chain_law_map_prefix_apply_singleton` 在有限离散字母上取初态 $p$ 和常值核 $p$ 给长度 $n+1$ 的 iid 乘积，空词单独由归一化处理，保留该来源的 Tau Ceti 与 Apache-2.0 归属；它没有证明回返初态或平稳律等价。

有限条件信息充分性只约束同一联合律的正先验状态；提升到全部有限状态的核分解须保留逐点正先验。它们不是无限路径的拓扑支撑或有效延拓定理。逐点与几乎处处分离声明中的非空目标条件、Lebesgue 非概率反例，以及有限边缘全可实现而有限支撑读数像零测且非闭的例子，仍分别按第 4.8.3 节的准确范围理解，不替代本章的零质量柱反例、逆向采样或预算模量证明。

这些是普通数学证明和既有结果的应用，不是新增 Lean 核验；全面新颖性文献核对未完成，因而不主张原创性。一般非 iid 过程、无限字母表、原始位置平稳 Parry 初始混合、任意非恒定预算的必要充分分类、一般局部预算分类、最优余量的闭式及最优运行时，都未由本章解决。可计算最优值不附带一般实数名下的精确选择器。所有正余量及接口结论都保留实际字母数、正坐标、无根、深度预算和同一共同实现；没有把有限层正确性变成无限点有限正认证，也没有推出 E7、有限覆盖、逻辑独立性或物理空间、时间、频率、熵产生之间的身份结论。

## 追加锚（本行以下为增补区）

## 6. 历史依赖、熵阈值与停止代价

本章在第 5 章的实际词树上研究三个问题：允许历史改变下一步概率时，哪一种律与禁词族联合删除最多质量；深度预算的增长怎样与自信息竞争；满测截获需要怎样的停止长度和有限状态资源。所有长度均为原始输出字母数，所有对数均为自然对数。第 5 章的 iid 结果、数值与有效接口继续由原节承担；本章只在明确的参数代入处调用它们。

### 6.1 原始词树、任意预算与历史联合极值

**定义 6.1.1（同一树上的四种质量）。** 沿用定义 5.1.1：实际字母表 $A$ 有 $d\ge2$ 个字母，$b_n\in\mathbb N$ 是每个正深度的不同禁词数上界。$\mathcal C_b$ 是满足 $|F\cap A^n|\le b_n$ 的无空词前缀码族，允许空族和跳层。令
$$
U_F=\bigcup_{w\in F}[w],\quad E_F=A^{\mathbb N}\setminus U_F,
\quad S_\mu(F)=\sum_{w\in F}\mu[w]=\mu(U_F).
$$
有限截断 $F_{\le N}$ 的补集 $E_{F,N}$ 是 clopen，且 $E_{F,N}\downarrow E_F$。原始库存可以重复公告或含祖先后代；取最终前缀极小不同词保持柱并、减少各层词数，正如第 5.5 节。有限阶段能有效做此操作，最终极小族不因此可枚举，最终无禁祖先也不因此可判。

固定正归一 iid 向量 $p$，写 $p(w)=\prod_i p_{w_i}$、$m=\max_a p_a<1$，并定义
$$
M_N(p,b)=\max_{F\in\mathcal C_b,\ |w|\le N}S_p(F),\qquad
M_b(p)=\sup_{F\in\mathcal C_b}S_p(F).
$$
有限候选保证第一个最大值存在，$M_0=0$。固定 $0<\delta\le1/d$，$\mathcal Q_\delta$ 为每个有限历史 $v$ 的行 $q(a\mid v)\ge\delta$ 的所有过程，令 $r=1-(d-1)\delta$。其柱质量为沿实际路径的行乘积，每行坐标在 $[\delta,r]$ 中；不要求平稳、混合、有限记忆或可计算。定义
$$
\Gamma(d,\delta,b)=1-\sup_{q\in\mathcal Q_\delta,F\in\mathcal C_b}\mu_q(U_F).
$$
固定隐藏模型的 $\eta_b(p,K)$ 在定义 6.3.1 中另定；指定库存的 $\mu_q(E_F)$ 又与这些优化值不同。记 $B_N=\sum_{1\le n\le N}b_nd^{-n}$、$B=\sum_{n\ge1}b_nd^{-n}$，可取无穷。预算增长率约定为 $\beta=\limsup_n n^{-1}\log\max(1,b_n)$，故零预算和有限支撑的 $\beta=0$；对严格正熵的低增长条件，用 $\log0=-\infty$ 给同一判定。

**定理 6.1.2（同一个无限 iid 贪心码）。** 在每层固定一个质量优先、并列按预定全序的选择规则。令 $L_0^+=\{\varnothing\}$，由 $L_{n-1}^+$ 扩展得到选择前活前沿 $L_n^-$；从中选取 $k_n=\min(b_n,|L_n^-|)$ 个最重词 $G_n$，再令 $L_n^+=L_n^-\setminus G_n$。这样得到的 $G=\bigcup_{n\ge1}G_n$ 不依赖终点，并满足
$$
S_p(G_{\le N})=M_N(p,b),\qquad S_p(G)=M_b(p).
$$
这包括预算零时不删、跳层、预算超过活数时选尽、空前沿以后始终为空及根终点 $N=0$；无需尾可和性、紧致性或目标连续性。

**证明。** 固定 $N$，从一个有限最优码出发，由浅到深对齐 $G$。浅层已对齐时，本层共同可选词正是 $L_n^-$。已选贪心词不动；若缺少贪心词 $u$，而旧码选了本层非贪心词 $v$，则 $p(u)\ge p(v)$。二者等长且活，子树不交；旧码含 $v$，故没有 $v$ 的严格后代。令 $\{uz:z\in Z\}$ 是旧码中 $u$ 的全部严格后代，$Z$ 是前缀自由的非空后缀族，$\alpha=\sum_{z\in Z}p(z)\le1$。把 $v$ 换成 $u$，把每个 $uz$ 换成 $vz$，质量改变量恰为
$$
p(u)+p(v)\alpha-p(v)-p(u)\alpha=(p(u)-p(v))(1-\alpha)\ge0.
$$
每个搬移词长度不变，$v$ 子树原本无其他选词；两子树之外的词均不可与搬入词发生前缀冲突，浅层活性又排除了已选祖先。因此前缀自由、所有深度预算及既有浅层对齐均保持。

若旧层没有可换的非贪心词，旧层选词就是 $G_n$ 的真子集，尚有空槽。加入 $u$ 并删掉它的所有选中后代，增益为 $p(u)(1-\alpha)\ge0$；本层仍不超过 $b_n$，深层数只减，前缀自由保持。相同词的分支无需变更。每次增加本层与 $G_n$ 的交集，有限次后本层对齐。处理完 $N$ 层得到 $G_{\le N}$，最优性保持。这同时包含第 5.4 节 $b_n=1$ 的交换和空槽两分支，未把该节推广前的共同 iid 尾假设省掉。

对任意无限合法 $F$，非负可数可加性给
$$
S_p(F)=\lim_N S_p(F_{\le N})\le\lim_N M_N(p,b)
=\lim_N S_p(G_{\le N})=S_p(G).
$$
同一 $G$ 的前缀一致性已由构造保证；这里没有从一列互不相容的有限最优码猜出无限码。证毕。

**推论 6.1.3（均匀饱和）。** 令 $u_a=1/d$。若 $s_n=S_u(G_{\le n})$，整数活数给
$$
|L_n^-|=d^n(1-s_{n-1}),\quad
s_n=s_{n-1}+\min\{b_nd^{-n},1-s_{n-1}\},\quad
|L_n^+|=d^n(1-s_n).
$$
归纳得 $M_N(u,b)=\min(1,B_N)$，取极限得 $M_b(u)=\min(1,B)$。$B>1$ 时某个有限层耗尽；$B=1$ 时可以仅在无限极限达到质量一，仍留无限路径。质量一与逐路径删尽是不同结论。

**定理 6.1.4（历史类的联合极值）。** 令 $p^*=(r,\delta,\ldots,\delta)$。对每个 $q,F,N$，
$$
\mu_q(U_{F_{\le N}})\le M_N(p^*,b),\qquad
\sup_{q,F}\mu_q(U_F)=M_b(p^*),\qquad
\Gamma(d,\delta,b)=1-M_b(p^*).
$$
最后的联合最优由同一个 iid 律 $p^*$ 和定理 6.1.2 的无限码实际取得。

**证明。** 先固定有限 $F$。选中节点取值一，深度 $N$ 未选叶取零；未选内节点的子树最优值为 $V_a$。各历史行独立可选，故逆向归纳的 Bellman 运算是
$$
\max_{x_a\ge\delta,\ \sum x_a=1}\sum_a x_aV_a
=\delta\sum_aV_a+(1-d\delta)\max_aV_a.
$$
写 $x_a=\delta+y_a$，$y_a\ge0$、$\sum y_a=1-d\delta$ 即证明上界，全部余量放在一个最大子值上即取得。有限行同时选择；选中节点下及终点后的无关行任补成允许行。因此所得极端律 $q^*$ 可延长为整个无限过程。

在每个原节点 $v$ 选一个置换 $\pi_v$，把它的重子标签送到 $0$，递归定义
$$
\phi(\varnothing)=\varnothing,\qquad \phi(va)=\phi(v)\pi_v(a).
$$
由逐层归纳，$\phi$ 在每层是双射，保持长度，并双向保持祖先关系。故 $\phi(F)$ 仍前缀自由且逐深度预算不变。每条边有 $q^*(a\mid v)=p^*_{\pi_v(a)}$，沿路径相乘得 $\mu_{q^*}[w]=p^*(\phi(w))$。于是
$$
\mu_q(U_F)\le\mu_{q^*}(U_F)=\mu_{p^*}(U_{\phi(F)})\le M_N(p^*,b).
$$
这里允许码随重标号改变；反向因 $p^*\in\mathcal Q_\delta$ 且 iid 贪心可行。$\delta=1/d$ 时所有行均匀，置换任取，无需指定唯一重子。无限情形对每个 $F$ 截断取单调极限；辅助的有限优化行和置换不必随 $N$ 一致，承担实际无限取得的是固定的 $p^*,G$。证毕。

等价地，当 $\delta<1/d$，每行是有限骰子 $P^{(a)}(z)=\delta+(1-d\delta)\mathbf1_{z=a}$ 的凸组合，权为 $(q(a\mid v)-\delta)/(1-d\delta)$。均匀端点单独处理。此表示与 Bellman 的有限极点计算相符，不把外部有限骰子结论当成本章无限极值的证明。若合法码还有标签相关约束，$\phi(F)$ 未必合法；上述归约仅用于对这些树置换不变的预算类。

**例 6.1.5（固定律不能偷换为联合优化）。** 二元过程根行为 $(3/5,2/5)$，历史 $0$ 后行为 $(99/100,1/100)$，历史 $1$ 后行为 $(1/2,1/2)$，更深行任取正行，预算 $b_1=b_2=1$、其他为零。固定律贪心先取 $0$，再取 $10$ 或 $11$，质量 $3/5+1/5=4/5$；合法码 $\{1,00\}$ 的质量为 $2/5+(3/5)(99/100)=497/500$。共同 iid 后缀的交换等式在此没有适用前提。

有限隐藏反例取状态 $R,U,V,W$，初态 $R$，发射
$$
p_R=(2/5,7/20,1/4),\quad p_U=(49/50,1/100,1/100),\quad
p_V=p_W=(1/3,1/3,1/3).
$$
从 $R$ 发射 $0,1,2$ 后分别到 $U,V,W$，其余状态对任意发射均自环。相同二层预算的贪心取 $0$ 后，在 $1$ 子树取一个词，得 $2/5+7/60=31/60$；$\{1,00\}$ 给 $7/20+(2/5)(49/50)=371/500$。全部转移已给定，结构零不妨碍正发射。另在 $d=3,\delta=1/4,b_1=1$、其他预算零时，固定均匀律的最优删除是 $1/3$，历史类的联合最优是 $1/2$。这三种比较分别说明固定非 iid 贪心失效、隐藏后验尾不相同、固定律最优不同于类最优。

### 6.2 有限头运输、三种尾与熵阈值

**引理 6.2.1（保留实际条件尾的 Borel 比较）。** 给 $q\in\mathcal Q_\delta$ 和 $N\ge0$，令 $\nu_N$ 的前 $N$ 个条件行均匀，之后在每个实际历史上仍用 $q$ 的原行。对所有 Borel 集 $D$，
$$
(d\delta)^N\nu_N(D)\le\mu_q(D)\le(dr)^N\nu_N(D).
$$
**证明。** 对 $v\in A^N$，令 $D_v$ 是 $D$ 在柱 $[v]$ 的尾截面，$\kappa_v$ 是该历史后的实际条件尾律。两律在此使用相同的 $\kappa_v$，故
$$
\mu_q(D)=\sum_{|v|=N}\mu_q[v]\kappa_v(D_v),\qquad
\nu_N(D)=\sum_{|v|=N}d^{-N}\kappa_v(D_v).
$$
将 $\delta^N\le\mu_q[v]\le r^N$ 代入即可；$N=0$ 是同一律。条件尾的 Borel 一致性来自所有尾柱乘积一致及概率测度唯一性。这里没有断言 $\mu_q$ 与无限均匀 iid 律互相绝对连续。证毕。

**定理 6.2.2（最大字母尾下的精确 Kraft 阈值）。** 写
$$
W_N=\sum_{n>N}b_nr^n.
$$
若 $W_N\to0$，则对所有 $q,F$ 和 $N\ge0$，
$$
\mu_q(E_F)\ge(d\delta)^N
\left[1-B_N-(dr)^{-N}W_N\right]_+.
$$
在这一可和范围内，$\Gamma(d,\delta,b)>0$ 当且仅当 $B<1$；$B\ge1$ 时，有一个只依赖 $d,b$ 的码对全部这些历史律都满测。

**证明。** 在 $\nu_N$ 中，长度 $n\le N$ 的禁词质量是 $d^{-n}$；长度 $n>N$ 时至多 $d^{-N}r^{n-N}$。短柱不交、长柱并集上界给 $\nu_N(E_F)\ge[1-B_N-(dr)^{-N}W_N]_+$，用引理 6.2.1 即得式子。

也可直接计数。设 $\mathcal H_N$ 为未被长度至多 $N$ 禁词删掉的 $N$ 词，$f_n=|F\cap A^n|$，则
$$
|\mathcal H_N|=d^N\left(1-\sum_{n\le N}f_nd^{-n}\right)\ge d^N(1-B_N).
$$
令 $e_v$ 为在 $v\in\mathcal H_N$ 后继续幸存的条件概率。每个长禁词属于唯一活历史，每个后缀条件质量至多 $r^{n-N}$，故 $\sum_{v\in\mathcal H_N}(1-e_v)\le r^{-N}W_N$。于是 $\mu_q(E_F)=\sum_v\mu_q[v]e_v\ge\delta^N\sum_ve_v$ 给同一个正部下界。这独立计数证明也适用于 $N=0$。

因 $dr\ge1$，若 $B<1$，取 $W_N<1-B$ 即使括号严格正，给一个对整个类共同的正数。可和性还蕴含 $B<\infty$。若 $B\ge1$，用推论 6.1.3 的均匀饱和码。$B>1$ 有限耗尽，故每个过程逐路径删尽。$B=1$ 若不曾有限耗尽，每层用满预算，选择后活数为
$$
|L_N^+|=d^N(1-B_N)=d^N\sum_{n>N}b_nd^{-n}.
$$
任意允许过程在这些活柱的质量至多
$$
|L_N^+|r^N=\sum_{n>N}b_nr^n(dr)^{N-n}\le W_N\longrightarrow0,
$$
其中 $N-n<0$ 且 $dr\ge1$ 决定了方向。故该码满测，未必删掉每条路径。证毕。

次指数预算时，这个仅依赖 $d,b$ 的饱和码对每个具有某个共同正条件下界的过程均满测：对每个过程使用其自己的 $\delta,r$ 验证几何尾即可，过程之间不要求共用同一个数值下界。

对固定 $F$，以实际数 $f_n$ 代入，若 $\sum_nf_nr^n<\infty$，则 Kraft 不等式给 $\sum_nf_nd^{-n}\le1$，且对每个允许 $q$，$\mu_q(U_F)=1$ 当且仅当该和为一：小于一用上述正界，等于一用实际活数公式。不可将这条结论扩展到没有其自身加权尾的任意码。

第 5.1 节次指数条件 $\forall a>1\ \exists N_0\ \forall n\ge N_0:b_n\le a^n$ 蕴含上述尾前提。更弱的一个最终界 $b_n\le a^n$、$ar<1$ 已足够，且 $N\ge N_0$ 时
$$
W_N\le\frac{(ar)^{N+1}}{1-ar}.
$$
此时 $a<1/r\le d$。存在这样的 $N_0$ 与能输入或算出它是两件事。

**适配与命题 6.2.3（原连续性合同及历史扩展）。** 第 5.2 节的 iid 论证保留其完整次指数前提；本章历史与隐藏扩展也在邻域统一指数尾下成立，普通可和性不足以替代它。

具体地，定理 5.2.1–5.2.2 对固定 iid $F$ 的现有证明按下列常数使用：在正单纯形内取邻域 $\max q_a\le r_0<1$ 和 $1<a<1/r_0$，有限多项式头加 $\sum_{n>N}b_nr_0^n$ 的一致几何尾证明连续性，故满测集合 $Z_F=\{p:S_p(F)=1\}$ 相对闭。若 $p\in Z_F$，$m=\max p_a$，取 $am<1$ 和相应 $N_0$，有限剩余 clopen 的比较常数 $C(q,p)=\max_a q_a/p_a$ 给
$$
\mu_q(E_F)\le\mu_q(E_{F,N})\le C(q,p)^N\mu_p(E_{F,N})
\le\frac{am}{1-am}(C(q,p)am)^N.
$$
在 $C(q,p)am<1$ 的邻域让 $N\to\infty$，得到相对开性。连通正单纯形与均匀端点 $S_u(F)\le B<1$ 排除满测。其量词是每个固定正 $p$ 对全部 $F$ 的 gap，不是全部 $p$ 共用一个数；$b_n=1$ 的旧尾恰为 $m^{N+1}/(1-m)$，$d\ge3$ 时均匀端点为 $1/(d-1)<1$。

码空间仍用 $\prod_n\{S\subseteq A^n:|S|\le b_n\}$，每项有限离散且含空集；一词特例为空层符号 $\bot$。任何前缀违例有有限两层见证，合法子空间闭紧。有限头连续、尾对全码一致，故目标连续并取得最大值；把逐码严格性用于最大化码才得到共同 gap。这是原证明的逻辑链，定理 6.1.2 的无尾取得不删除其连续性内容。

历史律取 $q_t(a\mid v)=(1-t)/d+tq(a\mid v)$，$t\in[0,1]$。行始终在 $[\delta,r]$，相邻参数行比至多 $1+|t-s|/\delta$。有限截断依赖有限多行且对 $t$ 连续；次指数尾可先选 $ar<1$。若 $q_t$ 对固定码满测，用长度 $N$ 似然比 $C^N$ 与 $\rho^{N+1}/(1-\rho)$，$\rho=ar$，在 $C\rho<1$ 的相邻参数范围得满测集相对开，闭性来自统一尾。连通区间及 $t=0$ 均匀端点排除满测。全部行的乘积空间 $\mathcal Q_\delta$ 紧，和码空间的联合有限头连续，统一尾证明联合目标连续并取最大，故给全类 gap。隐藏发射的对应展开在第 6.3 节给出。以上开性都用了指数放大后的尾趋零；仅知道 $W_N\to0$ 不能断言 $C^NW_N\to0$。

**定理 6.2.4（Rényi 的辅助头尾与原律尾）。** 令 $s>1$、$\theta=(s-1)/s$。对 iid $p$ 令
$$
Z_s=\sum_ap_a^s,\quad H_s=-\frac{\log Z_s}{s-1};
$$
对整个历史类取 $Z_s=r^s+(d-1)\delta^s$ 及相同定义的 $H_s=H_s(p^*)$。若全深度预算有包络 $b_n\le C e^{\beta_0n}$，$C\ge1$，$\beta_0<H_s$，记 $\rho=e^{-\theta(H_s-\beta_0)}<1$，则辅助均匀头律的长词尾满足
$$
R_N=C^\theta e^{-\theta(\log d-\beta_0)N}\frac{\rho}{1-\rho},
\qquad
\mu(E_F)\ge(d\ell)^N[1-B_N-R_N]_+,
$$
其中 iid 时 $\ell=p_{\min}$，历史类时 $\ell=\delta$。另在原律中，
$$
\sum_{\substack{w\in F\\|w|>N}}\mu[w]\le
T_N:=C^\theta\frac{\rho^{N+1}}{1-\rho}.
$$
$W_N,R_N,T_N$ 分别是最大字母尾、辅助头尾、原律尾，不互相代名；最后一式才直接控制原律截断和真外体积误差。

**证明。** iid 的 $k$ 步词概率 $s$ 次幂和为 $Z_s^k$。历史情形，每行是定理 6.1.4 后的极点凸组合，$\sum x_a^s$ 凸，故每行幂和至多 $Z_s$。对同一实际历史的后缀，递归展开最后一行即将 $k$ 步幂和界乘以 $Z_s$，归纳得至多 $Z_s^k$，没有拼接不同过程的边缘最优值。

在引理 6.2.1 的均匀头之后，长度 $N+k$ 的幂和至多 $d^{N(1-s)}Z_s^k$，iid 时等号。有限 Hölder 给任意至多 $b_{N+k}$ 个词的总质量上界
$$
b_{N+k}^{\theta}d^{-N\theta}Z_s^{k/s}
\le C^\theta e^{-\theta(\log d-\beta_0)N}\rho^k.
$$
从 $k=1$ 求几何和得 $R_N$。短词至多 $B_N$，乘有限头密度下界即得正部证书。

原律的全层幂和直接至多 $e^{-(s-1)H_sn}$，所以任何至多 $b_n$ 个词的集合质量至多 $b_n^\theta e^{-\theta H_sn}\le C^\theta\rho^n$。这一层界不要求前缀自由；对长层用并集上界并求几何和得 $T_N$。证毕。

有限和微分给 $Z_1=1$、$Z'_1=\sum p_a\log p_a$，从而 $\lim_{s\downarrow1}H_s=H(p)=-\sum p_a\log p_a$。Jensen 给 $Z_s\ge d^{1-s}$，故 $H_s\le\log d$。因此若 $\beta<H(p)$，可选 $\beta<\beta_0<H_s(p)$；limsup 给最终包络，有限早期项吸收入某个 $C\ge1$。此时 $R_N\to0$，若 $B<1$ 则某个括号严格正，得到共同 gap，无须 $W_N$ 可和。历史类以 $h_*=H(p^*)$ 代入得到相同结论，控制量不是某个任意历史律的最终熵率。在 $B<1$ 的域内，$b_nd^{-n}<1$ 给 $\beta\le\log d$。

**定理 6.2.5（严格超熵时的首次进入码）。** 若 $\beta>h=H(p)$，选 $h<\gamma<\beta$。有无限多个确定深度 $n$ 满足 $b_n\ge e^{\gamma n}$。在这些深度、任意指定延迟 $L$ 后取候选
$$
D_n=\{w\in A^n:p(w)\ge e^{-\gamma n}\}.
$$
每个候选至少该质量，而全层质量一，故 $|D_n|\le\lfloor e^{\gamma n}\rfloor\le b_n$。取全部候选的首次进入词，即删除有更短候选祖先者；前缀自由、层数不增，且柱并不变。自信息增量有界可积，iid 强大数律给 $-n^{-1}\log p(X_{\le n})\to h<\gamma$，故几乎每条路径在所有足够大的启用深度入选，首次进入码满测。

若 $p$ 非均匀，可再令 $\gamma<\log d$。其实际均匀 Kraft 和至多 $\sum_{n\ge L}(e^\gamma/d)^n=(e^\gamma/d)^L/(1-e^\gamma/d)$，随延迟趋零。若另构造从 $L$ 起的向上取整预算 $\lceil e^{\gamma n}\rceil$，预算本身的 Kraft 上界还要加 $d^{-L}/(1-d^{-1})$，不可丢弃。一般超熵预算只保证无限多个充分深度，不保证所有晚层都充分。历史类的零 gap 由允许的 iid $p^*$ 实现；不是每个固定历史律都满测。均匀律始终按推论 6.1.3 的精确公式处理。

**边界 6.2.6（常数预算与参数面）。** 第 5.7 节以 $b_n=c$ 代入给 $B=c/(d-1)$：$c<d-1$ 时每个固定正 iid 律及固定 $\delta$ 类均有共同 gap；$c=0$ 唯一空码的 gap 为一。$c\ge d-1$ 时码 $\{a^{n-1}z:z\ne a,n\ge1\}$ 每层 $d-1$ 词，补集为 $\{a^\infty\}$。iid 删除质量 $\sum_{n\ge1}p_a^{n-1}(1-p_a)=1$；任意允许历史律的剩余前缀质量至多 $r^N\to0$，所以仍满测。二元 $c=1$ 是端点；对 $p^*=(r,\delta)$ 的贪心梳 $\{1^{n-1}0\}$，和为 $\sum r\delta^{n-1}=1$。

正向一词分类的 $d\ge3$ 不能省；亦无整个开放单纯形共用的正数：$c\ge1$ 时单字母码 $\{a\}$ 已在 $p_a\to1$ 时使 gap 趋零。第 5.7 节更精确的三元面族 $p^{(\varepsilon)}=(a(1-\varepsilon),(1-a)(1-\varepsilon),\varepsilon)$，$0<a<1$，沿二元梳的幸存量为 $\varepsilon/(1-a+a\varepsilon)\to0$。固定正参数下的有效算法不等于所有正参数共用一个数。第 4.6 节及第 5.8 节的 Hölder/Rényi 与 $H(p)>\log2$ 一词充分证书仍有定量用途；这里的 $\beta<H(p)$ 是预算增长条件，不是把旧熵阈值重命名。

### 6.3 隐藏准备、后验尾与移位局部合同

**定义 6.3.1（先发射、后更新）。** 状态集 $S$ 有限非空，发射满足 $p_s(a)>0$、$\sum_ap_s(a)=1$，更新 $K(s,a,t)\ge0$、$\sum_tK(s,a,t)=1$，允许结构零；初态 $\alpha$ 是任意状态分布。把行向量置左，定义
$$
M_a(s,t)=p_s(a)K(s,a,t),\quad M_w=M_{w_1}\cdots M_{w_n},\quad
M_\varnothing=I,\quad \mu_\alpha[w]=\alpha M_w\mathbf1.
$$
非负矩阵及 $\sum_aM_a\mathbf1=\mathbf1$ 给柱的一致性和根质量一，确定唯一输出律。完整隐藏路径展开是
$$
\mu_\alpha[w]=\sum_{s_0,\ldots,s_n}
\alpha(s_0)\prod_{i=1}^n p_{s_{i-1}}(w_i)K(s_{i-1},w_i,s_i).
$$
令 $\ell=\min_{s,a}p_s(a)>0$、$r_p=\max_{s,a}p_s(a)<1$。每个输出历史后的状态后验是分布，下一输出行是各发射行的凸组合，所以条件概率在 $[\ell,r_p]$，特别 $\ell^{|w|}\le\mu_\alpha[w]\le r_p^{|w|}$。它也在 $\mathcal Q_\ell$，该类的上界 $1-(d-1)\ell$ 可比 $r_p$ 大。

在以下次指数预算且 $B<1$ 的固定模型结论中，定义
$$
\eta_b(p,K)=1-\max_{s\in S}\max_{F\in\mathcal C_b}\mu_{e_s}(U_F).
$$
**命题 6.3.2（固定模型的取得与任意初态）。** 上式最大值取得且 $\eta_b(p,K)>0$；对全部 $\alpha,F$，$\mu_\alpha(E_F)\ge\eta_b(p,K)\ge\Gamma(d,\ell,b)$。这不是固定模型与历史类的等式。

**证明。** 若 $b_n\le a^n$ 最终成立且 $ar_p<1$，每个 $\alpha,F$ 的长词质量至多 $(ar_p)^{N+1}/(1-ar_p)$，起点 $N\ge N_0$ 保留。固定 $K,\alpha$，把发射 $p$ 改成 $q$ 时，隐藏展开中只改变发射因子；取 $C(q,p)=\max_{s,a}q_s(a)/p_s(a)$，每条路径至多乘 $C(q,p)^n$。含零 $K$ 或零初态权的项两侧同为零，不曾除以转移概率。因此所有长度 $n$ 柱及其有限并均有同一比较。

发射空间是有限个开放正单纯形的乘积，连通。有限截断是发射坐标的多项式；在邻域取统一发射上界 $r_0<1$ 和最终包络 $ar_0<1$，统一尾证明连续、满测集相对闭。若在 $p$ 满测，有限剩余量至多 $(ar_p)^{N+1}/(1-ar_p)$；刚才的比较使邻域剩余量至多 $ar_p(C ar_p)^N/(1-ar_p)$。在 $C ar_p<1$ 时趋零，故满测集相对开。此处仍不能把最终指数界替换为普通可和性。

均匀发射时 $M_a=d^{-1}K_a$，每个随机矩阵 $K_a$ 保 $\mathbf1$，故对任意 $w,\alpha$ 都有 $\alpha M_w\mathbf1=d^{-|w|}$。这给严格 iid 均匀输出，并非只检验均匀边缘。由于 $B<1$，该端点不满测，连通性排除任意固定 $F,\alpha$ 的满测。再用第 6.2.3 节的同一闭紧码空间：每个纯初态目标由统一尾连续，取得最大；有限状态再取最大仍严格小于一。最后 $\mu_\alpha(E_F)=\sum_s\alpha_s\mu_{e_s}(E_F)$，给任意混合的共同 gap。每个隐藏输出属于 $\mathcal Q_\ell$，所以 $\eta_b\ge\Gamma$。证毕。

若只为取得正界，也可直接把第 6.2 节的 $W$ 或熵合同用于 $\delta=\ell$；这扩展了充分条件，但不把上面的发射同伦证明改成无尾连续性结论。$d\ge3,b_n=1$ 以及二元适当稀疏预算都是其原次指数特例。

**命题 6.3.3（查询必须使用移位预算与实际后验）。** 固定查询 $v$，$h=|v|$。若最终库存有 $w\preceq v$（包括 $w=v$），则 $E_F\cap[v]=\varnothing$。否则只有严格后代 $vu$ 会删到该柱，$u\ne\varnothing$，尾码 $F_v=\{u:vu\in F\}$ 的预算为
$$
b^{[h]}_n=b_{h+n}.
$$
历史条件律为 $q^v(a\mid z)=q(a\mid vz)$，仍在 $\mathcal Q_\delta$。隐藏条件初态恰为
$$
\beta_v=\frac{\alpha M_v}{\alpha M_v\mathbf1},\qquad
\mu_\alpha[vu]=\mu_\alpha[v]\,\beta_vM_u\mathbf1.
$$
分母至少 $\ell^h>0$，$M_v$ 包含最后一个字母发射后的更新，不能删去最后一个 $K$。

这些等式由 $M_{vu}=M_vM_u$ 及 $\beta_v\mathbf1=1$ 直接给出。在移位预算满足命题 6.3.2 的合同时，令 $\eta_s^{[h]}=1-\max_{G\in\mathcal C_{b^{[h]}}}\mu_{e_s}(U_G)$，则保留较强的后验加权界
$$
\mu_\alpha(E_F\cap[v])
=\mu_\alpha[v]\sum_s\beta_v(s)\mu_{e_s}(E_{F_v})
\ge\mu_\alpha[v]\sum_s\beta_v(s)\eta_s^{[h]}
\ge\mu_\alpha[v]\min_s\eta_s^{[h]}.
$$
历史类版本是 $\mu_q(E_F\cap[v])\ge\mu_q[v]\Gamma(d,\delta,b^{[h]})\ge\delta^h\Gamma(d,\delta,b^{[h]})$。一个查询的数值界不会自动建立全部查询的接口。

移位输入的明确转换如下。最大字母尾满足
$$
W_N^{[h]}=\sum_{n>N}b_{h+n}r^n=r^{-h}W_{h+N}.
$$
全深度指数包络 $b_n\le Ca^n$ 变为 $b_{h+n}\le(Ca^h)a^n$；第 6.2.4 节保留相同 $s,\log a<H_s,\rho$，只把 $C$ 替换为 $Ca^h$。若是最终包络，起点也须保留或先吸收早期项。对第 5.5.5 节的有效次指数输入 $\nu_{\rm bud}$，给 $a>1$ 先取 $1<t<a$，计算 $N_1$ 使 $(a/t)^{N_1}\ge t^h$，则
$$
\nu_h(a)=\max\{1,\nu_{\rm bud}(t),N_1\}
$$
保证 $n\ge\nu_h(a)$ 时 $b_{h+n}\le t^{h+n}\le a^n$。这些转换均另需
$$
B^{[h]}=\sum_{n\ge1}b_{h+n}d^{-n}<1;
$$
根处 $B<1$ 不能代替它。有了实际尾输入才有有效局部界，仅有语义次指数承诺不给可提取模量。常数预算 $c<d-1$ 的移位不变，故全部无禁祖先柱可共用同一条件 gap。

在移位 $W^{[h]}$ 可和的范围内，对所有无禁祖先局部库存有共同正条件 gap 当且仅当 $B^{[h]}<1$。充分性是定理 6.2.2 代入 $q^v,b^{[h]}$；若 $B^{[h]}\ge1$，把该定理的饱和尾码 $G$ 前接 $v$，得 $vG$，绝对层数不超过 $b_{h+n}$、没有 $v$ 的禁祖先，条件删除满测，排除共同正界。这是全族判据，不是某一个指定库存的延拓判定程序。

**例 6.3.4（两个不同的局部失败）。** 取 $d=3,b_2=3$、其他零，$F=\{00,01,02\}$。$B=1/3$ 且无 $0$ 的禁祖先，但 $U_F=[0]$，查询柱全空。另取任意 $h\ge1$、$v\in A^h$ 和字母 $a$，令
$$
F=\{va^{n-1}z:n\ge1,z\ne a\},\qquad
b_{h+n}=d-1\ (n\ge1),\quad b_j=0\ (j\le h).
$$
首次非 $a$ 的位置唯一，证明前缀自由及
$$
B=d^{-h}<1,\quad B^{[h]}=1,\quad
E_F=(A^{\mathbb N}\setminus[v])\cup\{va^\infty\}.
$$
任意共同正下界历史律在该单点的质量至多 $\mu_q[v]r^N\to0$，所以 $\mu_q(E_F)=1-\mu_q[v]>0$，但 $E_F\cap[v]$ 非空零测，幸存点不属限制律支撑。这正是第 5.7.4 节 iid 反例的实际条件尾推广。第 5.7.1 节二元梳去掉第一个禁词还给 $E=[1]\cup\{0^\infty\}$、$M=p_1$ 及非空零测的 $[0]$ 切片。全局 gap 不能建立支撑等号。

**例 6.3.5（平稳不等于 iid，转移零不等于发射零）。** 取 $S=A=\{0,1,2\}$、$\alpha=(1/3,1/3,1/3)$，$p_s(a)=1/2$ 若 $a=s$，否则 $1/4$；$K(s,a,t)=\mathbf1_{t=a}$。状态转移矩阵双随机，均匀初态平稳；$\mu[0]=1/3$，输出 $0$ 后状态确定为 $0$，所以 $\mu[00]=(1/3)(1/2)=1/6\ne1/9$。发射下界 $\delta=1/4$，转移有许多零，仍满足全部隐藏合同。含零发射的表示不直接满足本节前提，但若其实际输出律另有共同条件下界，可直接按历史律使用第 6.2 节。任意非可计算 $\alpha,K$ 不影响已知 $\delta$ 的语义下界，却不自动提供 $\alpha M_w\mathbf1$ 的可计算名称；第 6.7 节算法保留这些实际输入。

### 6.4 信息谱、临界日程与停止长度

**命题 6.4.1（单层与跨层的信息谱）。** 固定正 iid $p$，令 $I_n=-\log p(X_{\le n})$、$h=H(p)$，$Z_n=I_n-nh$。设 $L_n(m)$ 是长度 $n$ 至多 $m$ 个词可有的最大质量，$L_n(0)=0$；$m\ge1,t\ge0$ 时
$$
\Pr(I_n\le\log m)\le L_n(m)\le\Pr(I_n\le\log m+t)+e^{-t}.
$$
**证明。** 质量至少 $1/m$ 的词至多 $m$ 个，全部选入给下界。对任意所选集合，把自信息超过 $\log m+t$ 的词分出，每个质量小于 $e^{-t}/m$，至多 $m$ 个给 $e^{-t}$；其余质量不超过所示事件概率，给上界。

更一般，禁用 $n<N$ 的预算记为 $b^{\langle N\rangle}$，其删除容量 $D_N=M_{b^{\langle N\rangle}}(p)$。令 $J_N=\{n\ge N:b_n>0\}$，任取 $t_n\ge0$，则
$$
\Pr\!\left(\bigcup_{n\in J_N}\{I_n\le\log b_n\}\right)
\le D_N\le
\min\!\left(1,\Pr\!\left(\bigcup_{n\in J_N}\{I_n\le\log b_n+t_n\}\right)+\sum_{n\in J_N}e^{-t_n}\right),
\qquad M_b(p)\le\min\left(1,\sum_nL_n(b_n)\right).
$$
左边把各层高质量候选全部前缀极小化；每条进入路径有最早的有限进入深度，故并集保持，层预算只减，确实是一份码。右边先固定同一 $F$，按首次命中词分高、低自信息；高质量部分落入所示事件并，低质量部分逐层不超过 $e^{-t_n}$，用并集界后才对 $F$ 取上确界。最后一式也是对同一码逐层相加。这没有深度事件独立性或各层最优同时可达的前提；发散的误差和只给平凡界。证毕。

**定理 6.4.2（每份确定无限子列上的临界截获）。** 若 $p$ 非均匀，则信息增量 $Y_i=-\log p_{X_i}-h$ 有界、独立同分布、均值零，方差 $V>0$；因为所有字母都有正质量，$V=0$ 当且仅当 $-\log p_a$ 在全部字母上恒定，恰等价于均匀。对每份预先固定的确定无限子列 $n_j$，
$$
\liminf_j\frac{Z_{n_j}}{\sqrt{n_j}}=-\infty\quad\text{几乎必然}.
$$
因此若在某确定无限深度集上 $\log b_n\ge nh-C\sqrt n$，$C<\infty$，则任意有限延迟以后都有实际满测的首次进入码。

**证明。** 对整数 $K\ge1$，中心极限定理给
$$
\Pr\{Z_{n_j}/\sqrt{n_j}<-K-1\}\longrightarrow
\Phi((-K-1)/\sqrt V)>0.
$$
任意事件列 $A_j$ 都有 $\Pr(\limsup A_j)=\lim_m\Pr(\bigcup_{j\ge m}A_j)\ge\limsup_j\Pr(A_j)$。因此事件 $E_K=\{\liminf_jZ_{n_j}/\sqrt{n_j}\le-K\}$ 有正概率。对任意固定 $m$，删掉前 $m$ 个增量只把该归一化和改动 $Z_m/\sqrt{n_j}\to0$，所以同一 liminf 可由 $Y_{m+1},Y_{m+2},\ldots$ 表达。$E_K$ 属每个尾 $\sigma$ 代数；独立增量的 Kolmogorov 零一律遂给 $\Pr(E_K)=1$。对可数整数 $K$ 取交得负无穷。此证明不把原始有限越界事件直接冒充尾事件。

取整数 $K>C$，几乎每条路径在任意延迟后的启用子列无限次满足 $I_n\le\log b_n$。命题 6.4.1 左边实际构造的首次进入码遂满测。概率一事件针对每份指定的确定子列；没有一个事件同时覆盖全部路径事后选择的子列的主张。证毕。

例如对任意 $r_0>0$、确定无限 $J$，延迟 $L$ 后在 $n\in J$ 置 $b_n=\lfloor e^{hn}n^{-r_0}\rfloor$、其他为零。最终括号内至少二，故取整使对数最多损失 $\log2$；$r_0\log n+\log2=o(\sqrt n)$，适用定理。其 $\beta=h$，均匀预算和至多 $\sum_{n\ge L}(e^h/d)^nn^{-r_0}\to0$。在启用层，单层容量却趋 $1/2$：命题 6.4.1 取 $t=n^{1/4}$，上下两个中心化阈值除以 $\sqrt{nV}$ 都趋零，CLT 的移动阈值结论可由固定 $\pm\epsilon$ 夹逼取得，且 $e^{-n^{1/4}}\to0$。单层半质量与首次进入最终全质量并不矛盾。

**命题 6.4.3（严格临界下穿的独立证明）。** 对同一非均匀 $p$，延迟 $L$ 后预算 $\lfloor e^{hn}\rfloor$ 也有满测码。这里另给不依赖子列定理的下穿证明。

取有界非退化均值零增量 $Y_i$，$|Y_i|\le K$。它必有一个负值 $y_-<0$ 的正概率。由位置 $x\in(0,M)$ 出发，选整数 $k$ 使 $k|y_-|>M$；任意连续 $k$ 个负值块都强迫退出 $(0,M)$。互不重叠块独立且各有固定正概率，故退出时间 $\sigma$ 几乎必然有限。对有界停时 $n\wedge\sigma$ 使用均值零鞅的停止等式，$\mathbb E S_{n\wedge\sigma}=x$；停止位置总在 $[-K,M+K]$，由支配收敛得 $\mathbb E S_\sigma=x$。若 $u_M$ 为上壁退出概率，则
$$
x\ge Mu_M-K(1-u_M),\qquad u_M\le\frac{x+K}{M+K}.
$$
对每个整数 $M>x$，排除已经证明为零的永不退出事件后，永不触及下壁的路径必须先到上壁；其概率不超过上式，令 $M\to\infty$ 得永不下穿概率零。条件化于延迟时刻的有限历史，若 $Z_L\le0$ 立即停止，否则从 $x=Z_L>0$ 应用刚才论证。因此从 $L$ 起首次 $Z_n\le0$ 几乎必然有限，其停止词满足 $p(w)\ge e^{-h|w|}$，每层至多 $\lfloor e^{hn}\rfloor$，前缀自由。其均匀 Kraft 和至多 $(e^h/d)^L/(1-e^h/d)$。只在有界停时上用停止等式，然后才取极限；没有假设原停止时间有限均值。证毕。

**命题 6.4.4（同主指数的另一侧）。** 非均匀 $p$ 的信息宽度 $R=\log(p_{\max}/p_{\min})>0$。令 $b_n=0$ 于 $n<L$，以后 $b_n=\lfloor e^{hn-n^{3/4}}\rfloor$。对任意本层至多 $b_n$ 个词，按阈值 $hn-n^{3/4}/2$ 分割，Hoeffding 给小自信息部分至多
$$
\Pr(Z_n\le-\tfrac12n^{3/4})\le e^{-\sqrt n/(2R^2)},
$$
其余每词质量小于 $e^{-hn+n^{3/4}/2}$，总计至多 $e^{-n^{3/4}/2}$。两条级数可和：对任意 $c,\alpha>0$，$n^\alpha/\log n\to\infty$ 使 $e^{-cn^\alpha}\le n^{-2}$ 最终成立。故 $L$ 足够晚时，所有合法码的总删除小于任意给定 $\varepsilon>0$，gap 至少 $1-\varepsilon$。同时 $\beta=h$，均匀 Kraft 和至多 $\sum_{n\ge L}(e^h/d)^n\to0$。对历史类把 $p=p^*$ 代入并用定理 6.1.4，得同一全类结论；此时要求 $\delta<1/d$。均匀端点 $R=0$ 不代入 Hoeffding 式，而由 $M_b(u)=\min(1,B)$ 处理。两种临界例证明主指数不足以分类，没有给任意临界日程的必要充分条件。

**定理 6.4.5（停止词的熵与平均长度）。** 对满测前缀码 $F$，停止时间 $\tau$ 几乎必然有限，停止词 $W$ 满足 $\Pr(W=w)=p(w)$，并有允许无穷的恒等式
$$
H(W)=\mathbb E I_\tau=h\,\mathbb E\tau.
$$
若 $\mathbb E\tau<\infty$，则熵 Kraft 和 $K_h(F)=\sum_{w\in F}e^{-h|w|}\ge1$。因此若 $\sum_nb_ne^{-hn}<1$，每份合法满测码都具有无穷平均长度。

**证明。** 前缀自由使停止词事件恰为对应柱，满测给总概率一。$\{\tau\ge i\}$ 由前 $i-1$ 个字母决定，与第 $i$ 个非负信息增量 $-\log p_{X_i}$ 独立。非负 Tonelli 给
$$
\mathbb E I_\tau=\sum_{i\ge1}\mathbb E[\mathbf1_{\tau\ge i}(-\log p_{X_i})]
=h\sum_{i\ge1}\Pr(\tau\ge i)=h\mathbb E\tau.
$$
若 $K_h=\infty$，所需不等式已成立；否则它严格正，定义可数分布 $Q(w)=e^{-h|w|}/K_h$。有限均值使 $I_\tau$ 和 $h\tau$ 可积，且
$$
\left|\log\frac{P_W(W)}{Q(W)}\right|\le I_\tau+h\tau+|\log K_h|.
$$
所以可数相对熵积分有意义，并精确等于 $-\mathbb E I_\tau+h\mathbb E\tau+\log K_h=\log K_h$。非负性也可直接由 $-\log x\ge1-x$、$x=Q(w)/P_W(w)$ 求期望取得，右边期望为零；这里 $Q/P_W$ 可积且均值一。故 $\log K_h\ge0$。若预算熵和小于一，$K_h(F)$ 不超过它，与有限均值的结论矛盾。证毕。

对 $r_0>1$ 的多项式缺口预算，足够延迟使熵和至多 $\sum_{n\ge L}n^{-r_0}<1$，而定理 6.4.2 仍给满测存在。一个可判实例是
$$
p=(1/2,1/4,1/4),\quad h=\log\sqrt8,\qquad
b_n=0\ (n<2),\quad b_n=\left\lfloor\frac{(\sqrt8)^n}{n^2}\right\rfloor\ (n\ge2).
$$
预算由整数式 $\operatorname{isqrt}(8^n\mathbin{//}n^4)$ 精确计算：对正实数 $x$，$\lfloor\sqrt x\rfloor=\operatorname{isqrt}(\lfloor x\rfloor)$。$p(w)\ge1/b_n$ 是有理比较，检查全部较短前缀即可决定首次进入码成员。定理 6.4.2 给满测；$\sum_{n\ge2}n^{-2}<\sum_{n\ge2}1/(n(n-1))=1$ 给所有合法满测码无穷均值。$n=2,\ldots,12$ 的预算依次为 $2,2,4,7,14,29,64,143,327,765,1820$；这些有限值不承担满测证明。

**例 6.4.6（Catalan 首次命中族）。** 在三元字母上把 $0$ 记为步长 $+1$，$1,2$ 为 $-1$。取从零首次到达 $+1$ 的词；其长度为 $2k+1$，最后一步必为 $+1$，此前 $2k$ 步非正并回到零。反射符号后是长度 $2k$ 的 Dyck 路，其数量 $C_k=\binom{2k}{k}/(k+1)$；$k$ 个负步各有两个字母标签，故
$$
b_{2k+1}=2^kC_k,\quad b_{2k}=0.
$$
首次命中保证前缀自由。对 iid 律 $p=(r,s,1-r-s)$，$0<r<1$、$0<s<1-r$，每个有 $k$ 个负步的 Dyck 符号形状，将全部 $2^k$ 个负步字母标记的权重求和，得 $(s+(1-r-s))^k=(1-r)^k$，故该层总质量为 $C_kr^{k+1}(1-r)^k$。首次返回分解给 $C(x)=1+xC(x)^2$，选择 $C(0)=1$ 的分支，得 $C(x)=(1-\sqrt{1-4x})/(2x)$；在 $x=1/4$ 由非负单调极限值为二。因此对所有这些正拆分都有
$$
\mu_p(U_F)=rC(r(1-r))=
\begin{cases}r/(1-r),&r<1/2,\\1,&r\ge1/2.\end{cases}
$$
均匀三元 $p=(1/3,1/3,1/3)$ 给实际 Kraft 和 $1/2$。中央二项式满足 $4^k/(2k+1)\le\binom{2k}{k}\le4^k$，故预算的 limsup 根增长为 $\sqrt8$。在负步两字母等分的对称特例中，$p=(1/2,1/4,1/4)$ 的熵恰为 $\log\sqrt8$，为临界满测实例；$p=(3/4,1/8,1/8)$ 的熵为 $(9/4)\log2-(3/4)\log3$，比 $\log\sqrt8$ 小 $(3/4)\log(3/2)>0$，是超熵实例。

对任意上述正拆分，步长仍以概率 $r,1-r$ 取 $+1,-1$。若 $r>1/2$，尚未命中到 $N$ 蕴含步长和 $S_N\le0$。对 $t=\tfrac12\log(r/(1-r))>0$，指数 Markov 不等式给
$$
\Pr(\tau>N)\le\Pr(S_N\le0)\le\mathbb E e^{-tS_N}
=(re^{-t}+(1-r)e^t)^N=(2\sqrt{r(1-r)})^N.
$$
$r=3/4$ 的尾是 $(\sqrt3/2)^N$。某参数下的指数停止尾没有使均匀参数也满测；这一族同时保留计数、生成函数、熵位置和停止尾四种信息。

### 6.5 有限状态资源与较弱过程前提的边界

**命题 6.5.1（吸收自动机的图二分）。** 设前缀码 $F$ 的右理想 $FA^*$ 由一份完全确定有限自动机识别，接受状态吸收。若每个可达非接受状态都能到接受状态，取这些最短到达路径长度的有限共同上界 $s\ge1$。在共同条件下界为 $\delta$ 的任意历史律下，每个尚未接受的 $s$ 步块至少以概率 $\delta^s$ 接受，所以
$$
\Pr(\tau>ks)\le(1-\delta^s)^k,\qquad
\mathbb E\tau=\sum_{n\ge0}\Pr(\tau>n)\le s/\delta^s.
$$
若有一个可达状态无法到接受状态，取其到达词 $v$，则整柱 $[v]$ 的后续都不接受，幸存量至少 $\mu[v]>0$。这证明满测与否是该吸收图的性质，对全部全正 iid 参数相同（取各自 $p_{\min}$），也对全部共同正下界历史律相同。论证按每块的条件概率迭代，不要求各块独立。空码只有坏状态；无根条件排除起点已接受的退化情形。

若 $B<1$，均匀律不可能满测，故任何合法满测码都非正则；正则 $F$ 会使 $FA^*$ 正则并给上述自动机，导致矛盾。仍在 $B<1$ 的条件下，若这份完全吸收自动机至多 $m$ 个状态，最短坏状态到达路径不重复状态，长度至多 $m-1$，所以
$$
\mu(E_F)\ge\delta^{m-1}.
$$
要求删除至少 $1-\varepsilon$，$0<\varepsilon<1$，遂必须 $\delta^{m-1}\le\varepsilon$，即 $m\ge1+\log(1/\varepsilon)/\log(1/\delta)$。所计的是识别右理想的这份自动机状态数，不是任意带外部存储程序的描述复杂度。

没有状态数上界时，若给定预算已经容纳某个在指定律下满测的合法码 $F$，其有限截断都合法且正则，删除质量趋一，自动机状态数可增长。这一近似结论有满测码存在的前提；第 6.2 节的次临界正 gap 预算不满足它，不能据此声称每个 $B<1$ 预算都无共同 gap。

**例 6.5.2（可计算满支持仍不足以替代共同下界）。** 固定 $d\ge3$，有效枚举所有有限词。逐个处理词 $v$：若 $[v]$ 与此前所选柱并相交则跳过；否则选 $v$ 的一个延长 $w_j$，长度严格超过此前所有选择且为正，加入其柱。有限词可比较前缀，算法有效；所选柱两两不交且每深度至多一个。每个基本柱在被处理时或已与并相交，或获得所选子柱，故 $U=\bigcup_j[w_j]$ 稠密。

均匀质量 $\lambda(U)\le\sum_{n\ge1}d^{-n}=1/(d-1)<1$。若仅有限选择，$U$ 会是既闭开又稠密的真子集，矛盾。因此 $w_j$ 是总可计算无限序列，长度严格增大。决定给定词是否为某 $w_j$ 时生成到长度超过它即可，故此码可判。

令 $\lambda_j$ 为均匀律在 $[w_j]$ 上的条件律，定义 $\nu=\sum_{j\ge0}2^{-(j+1)}\lambda_j$。对任意柱 $[v]$，其全部三种值为
$$
\lambda_j[v]=
\begin{cases}
1,&v\preceq w_j,\\
d^{-(|v|-|w_j|)},&w_j\prec v,\\
0,&v,w_j\text{ 不可比较}.
\end{cases}
$$
前 $J$ 项的遗漏不超过 $2^{-J}$，故柱质量一致可计算；稠密性使每个柱与某个选中柱相交，故每个柱质量严格正，$\nu$ 满支持。每个分量集中在 $U$，于是 $\nu(U)=1$。条件行 $\nu[va]/\nu[v]$ 也一致可计算且逐项严格正，正分母的计算用严格正下界搜索，不需统一下界。然而这些条件概率的下确界必为零：否则一词预算的 $B<1$ 与共同下界会由定理 6.2.2 强迫幸存正量，与 $\nu(U)=1$ 矛盾。这明确区分逐点正、满支持和统一正性。

**例 6.5.3（停止后转均匀的高最终熵率）。** 取非均匀正 iid $p_0$、$H(p_0)<\gamma<\log d$。定理 6.2.5 给从足够晚层起、增长指数 $\gamma$ 且 Kraft 和小于一的预算及一份 $p_0$-满测首次进入码 $F$。在尚无 $F$ 前缀的历史后使用 $p_0$，一旦已命中就永久使用均匀行。共同下界为 $\min_a p_0(a)$。每个停止词的严格前缀均未命中，所以新律 $q$ 下 $\mu_q[w]=p_0(w)$，从而 $\mu_q(U_F)=1$，停止时间几乎必然有限。

对 $n\ge\tau$ 的同一实际路径，自信息精确为
$$
-\log\mu_q[X_{\le n}]=-\log p_0(X_{\le\tau})+(n-\tau)\log d.
$$
有限的随机 $\tau$ 使样本每字信息趋 $\log d$。所有每字信息介于零与 $-\log\min p_0$，故对除以 $n$ 的信息用支配收敛，得到平均熵率也趋 $\log d$；不需 $\mathbb E\tau<\infty$。预算指数 $\gamma$ 小于这个最终熵率，却在这个固定历史律下删除满测，因此不能把 iid 定理的 $H(p)$ 换成任意历史律的最终熵率。历史类的定理依然用 $H(p^*)$。

可计算二元实例取 $p_0=(3/4,1/4)$，候选条件 $p_0(w)\ge(5/9)^{|w|}$，延迟后预算 $\lceil(19/10)^n\rceil$。这里 $e^{4H(p_0)}=256/27$，而
$$
(9/5)^4-256/27=17147/16875>0,\qquad 9/5<19/10<2.
$$
所以候选数量至多 $\lfloor(9/5)^n\rfloor$，在预算内，强大数律给满测；有理比较和有限前缀检查决定码及切换行。预算 Kraft 尾至多 $(19/20)^L/(1-19/20)+2^{-L}/(1-1/2)$，足够晚时小于一。最终熵率为 $\log2$，预算指数是 $\log(19/10)$。

名义三元向量 $(1/2,1/2,0)$ 实际只有两个正字母，二元梳即可满测；若允许空词，则单独禁根便删掉全部空间。这些是实际正字母数与正词长前提的直接边界，不涉及物理熵产生或时间身份。

### 6.6 压缩递推、活前沿与精确证书

**命题 6.6.1（压缩有限最优值）。** 对 $p^*=(r,\delta,\ldots,\delta)$，令 $a_n(k)$ 为本层选择后含 $k$ 个低概率字母的活词数，$a_0(0)=1$，越界项零。选择前的数及删除数为
$$
c_n(k)=a_{n-1}(k)+(d-1)a_{n-1}(k-1),\quad
e_n(k)=\min\left(c_n(k),\left[b_n-\sum_{j<k}e_n(j)\right]_+\right),\quad
a_n(k)=c_n(k)-e_n(k).
$$
由重字母的概率至少稀有字母概率，按 $k$ 增序删除就是定理 6.1.2 的一个固定并列规则，故
$$
M_N(p^*,b)=\sum_{n=1}^N\sum_{k=0}^ne_n(k)r^{n-k}\delta^k.
$$
计数只依赖 $d,b$，不依赖 $\delta$；均匀端点按同一规则仍最优。零预算和过大预算分别不删与耗尽。相同权重的词具有同一 iid 扩展计数，具体位置不影响下一层数值；如需实际词，须另行重建。预计算幂并逐层累加时为 $O(N^2)$ 次算术更新和 $O(N)$ 个当前层计数槽；整数位长、实数精度与生成词表的成本不在这个计数中。

一个独立有限描述是允许相对根预算的 $H_L(c_0,\ldots,c_L)$。$c_0\ge1$ 时选根，值一；$c_0=0,L=0$ 时值零。其余情形，对每个 $j=1,\ldots,L$ 将 $c_j$ 分配为 $d$ 个非负整数 $c_{j,a}$，$\sum_ac_{j,a}=c_j$，递归算子树值 $V_a=H_{L-1}(c_{1,a},\ldots,c_{L,a})$，然后取所有分配下 $\delta\sum_aV_a+(1-d\delta)\max_aV_a$ 的最大值。预算是上界，未使用槽可以任意分给子树，不排除任何可行码；反向把子码前接不同首字母即得到合法码，Bellman 极点行同时实现值。保存获胜分配、极点行及递归子树可重建见证，再独立逐柱乘积及逐边置换检查。这是另一种算法，不预设贪心。

**命题 6.6.2（选择后活前沿的误差）。** 对定理 6.1.2 的同一无限最优码，令 $t_N=\max_{v\in L_N^+}p(v)$；根层 $t_0=1$。若前沿空，全部未来误差恰为零，直接结束。否则当所示级数有限时，
$$
0\le M_b(p)-M_N(p,b)\le t_N\sum_{k\ge1}b_{N+k}m^k.
$$
**证明。** 每个未来贪心词 $w$ 有唯一长度 $N$ 的选择后活祖先 $v$，写作 $w=vz$，$|z|=k$，则 $p(w)\le t_Nm^k$。深度预算求和即得。$b_n=1$ 时误差是 $t_Nm/(1-m)$；$t_N\le m^N$，所以它相对旧最大字母尾的改善因子为 $t_N/m^N$。一般预算也有相同逐项比较。此处的活前沿属于这个最优 iid 码，不能套到每个实际库存或每个历史律；空前沿不写成无定义的 $0\cdot\infty$，发散级数也不给有限证书。证毕。

**证书 6.6.3（三个模型的原界与活前沿改进）。** 命题 5.4.2–5.4.3 仍承担原一词整数递推、标准库程序和完整旧整数数据。保持完全相同的 $(a,b,d,D,N)=(8,1,3,10,22),(18,1,3,20,73),(98,1,3,100,729)$，其中 $D=a+(d-1)b$，令 $R_n$ 为剩余质量的分母 $D^n$ 下整数分子。其原递推为 $R_0=1$、$R_n=DR_{n-1}-a^{n-k_n}b^{k_n}$，$k_n$ 是该层删词的稀有数。原证书为
$$
\frac{(D-a)R_N-a^{N+1}}{(D-a)D^N}>1/q_0,
\qquad q_0\in\{1000,10000,10000000\},
$$
即 $q_0((D-a)R_N-a^{N+1})-(D-a)D^N>0$。三项仍保留，不由改进值替换。

本层删完以后重新寻找最小活稀有数 $k_N^*$，设 $H_N=a^{N-k_N^*}b^{k_N^*}$，那么 $t_N=H_N/D^N$。不能一般地以最后删除的 $k_N$ 代替 $k_N^*$；本组三例碰巧分别同为 $3,4,4$。新的下界为
$$
L_N=\frac{(D-a)R_N-aH_N}{(D-a)D^N},\qquad
\Delta_{p/q}=q((D-a)R_N-aH_N)-p(D-a)D^N>0.
$$
相应目标是 $1567/50000,5520899/1250000000,1002739383/50000000000000$。第一项恰为 $L_{22}=61211/1953125=0.031340032$，比第一个目标多 $1/31250000$；其余完整精确分数及正整数余量在下方可执行数据中。这些是无限最优幸存量的下界，不是精确最优值。经定理 6.1.4，亦分别给 $d=3,\delta=1/10,1/20,1/100,b_n=1$ 的历史类下界。

三个低熵检验继续按命题 5.4.3 的整数不等式 $D^D<2^Da^ab^{(d-1)b}$；首例为 $10^{10}<2^{34}$。它们说明旧 $H(p)>\log2$ 充分证书不是一词正性的必要条件，不删除旧熵证书的定量意义。

下面的独立核对按整数质量聚类，不按稀有数聚类；每层同时检查 $R_n$、删除质量补数及活词数 $((d-2)d^n+1)/(d-1)$。数据保留完整整数、约分分数及十进制显示。所有比较只用整数或 `Fraction`；`Decimal` 不参与证明判定。将这个代码块单独保存为 Python 文件即可运行，它不读取外部数据或临时路径。

```python
import json
from fractions import Fraction
from decimal import Decimal, localcontext

def decimal_display(value: Fraction) -> str:
    with localcontext() as context:
        context.prec = 60
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def rational_record(value: Fraction) -> dict:
    return {
        'numerator': str(value.numerator),
        'denominator': str(value.denominator),
        'decimal_display': decimal_display(value),
    }


def certify(a: int, b: int, d: int, horizon: int,
            threshold_text: str) -> dict:
    if not (a > b >= 1 and d >= 3 and horizon >= 1):
        raise ValueError('Require a>b>=1, d>=3, horizon>=1')
    D = a + (d - 1) * b
    live = {1: 1}  # Integer probability numerator -> number of live nodes.
    mass_numerator = 1
    power_D = 1
    deleted_mass = Fraction(0)
    last_deleted_weight = None

    for depth in range(1, horizon + 1):
        expanded = {}
        for weight, count in live.items():
            expanded[weight * a] = expanded.get(weight * a, 0) + count
            expanded[weight * b] = (expanded.get(weight * b, 0)
                                    + (d - 1) * count)
        deleted_weight = max(expanded)
        expanded[deleted_weight] -= 1
        if expanded[deleted_weight] == 0:
            del expanded[deleted_weight]
        live = expanded
        mass_numerator = D * mass_numerator - deleted_weight
        power_D *= D
        deleted_mass += Fraction(deleted_weight, power_D)

        # A separate live-node sum checks the survivor recurrence.
        assert sum(weight * count for weight, count in live.items()) == mass_numerator
        # One deletion at every depth removes d^(depth-j) current leaves.
        assert (d - 1) * sum(live.values()) == (d - 2) * d ** depth + 1
        assert Fraction(mass_numerator, power_D) + deleted_mass == 1
        last_deleted_weight = deleted_weight

    largest_live_weight = max(live)
    rare_weights = [a ** (horizon - r) * b ** r
                    for r in range(horizon + 1)]
    r_min_after_deletion = rare_weights.index(largest_live_weight)
    r_last_deleted = rare_weights.index(last_deleted_weight)
    survivor = Fraction(sum(weight * count for weight, count in live.items()), power_D)
    t_N = Fraction(largest_live_weight, power_D)
    m = Fraction(a, D)
    tail = t_N * m / (1 - m)
    lower = survivor - tail
    threshold = Fraction(threshold_text)

    # Exact cross-multiplied certificate in the unreduced integer scale:
    # q*((D-a)*R_N - a*H_N) > p*(D-a)*D^N, threshold=p/q.
    lower_numerator_raw = (D - a) * mass_numerator - a * largest_live_weight
    lower_denominator_raw = (D - a) * power_D
    strict_margin = (threshold.denominator * lower_numerator_raw
                     - threshold.numerator * lower_denominator_raw)
    assert lower == Fraction(lower_numerator_raw, lower_denominator_raw)
    assert lower > threshold
    assert strict_margin > 0
    assert 0 < tail < survivor

    return {
        'parameters': {'a': a, 'b': b, 'd': d, 'D': D, 'N': horizon},
        'r_last_deleted': r_last_deleted,
        'r_min_after_deletion': r_min_after_deletion,
        'max_weight_live_node_count': str(live[largest_live_weight]),
        'R_N': str(mass_numerator),
        'H_N': str(largest_live_weight),
        'D_power_N': str(power_D),
        'lower_numerator_raw': str(lower_numerator_raw),
        'lower_denominator_raw': str(lower_denominator_raw),
        'finite_survivor': rational_record(survivor),
        't_N': rational_record(t_N),
        'improved_tail': rational_record(tail),
        'survivor_lower_bound': rational_record(lower),
        'strict_threshold': rational_record(threshold),
        'lower_bound_minus_threshold': rational_record(lower - threshold),
        'strict_comparison_integer_margin': str(strict_margin),
        'exact_lower_bound_strictly_above_threshold': strict_margin > 0,
        'all_depths_live_mass_equals_recurrence': True,
        'all_depths_survivor_plus_Fraction_deleted_mass_equals_one': True,
        'all_depths_total_live_node_count_checked': True,
    }


EXPECTED = json.loads(r'''
[
  {
    "parameters": {
      "a": 8,
      "b": 1,
      "d": 3,
      "D": 10,
      "N": 22
    },
    "r_last_deleted": 3,
    "r_min_after_deletion": 3,
    "max_weight_live_node_count": "37",
    "R_N": "313976780752303423488",
    "H_N": "144115188075855872",
    "D_power_N": "10000000000000000000000",
    "lower_numerator_raw": "626800640000000000000",
    "lower_denominator_raw": "20000000000000000000000",
    "finite_survivor": {
      "numerator": "74857897937847",
      "denominator": "2384185791015625",
      "decimal_display": "0.0313976780752303423488"
    },
    "t_N": {
      "numerator": "34359738368",
      "denominator": "2384185791015625",
      "decimal_display": "0.0000144115188075855872"
    },
    "improved_tail": {
      "numerator": "137438953472",
      "denominator": "2384185791015625",
      "decimal_display": "0.0000576460752303423488"
    },
    "survivor_lower_bound": {
      "numerator": "61211",
      "denominator": "1953125",
      "decimal_display": "0.031340032"
    },
    "strict_threshold": {
      "numerator": "1567",
      "denominator": "50000",
      "decimal_display": "0.03134"
    },
    "lower_bound_minus_threshold": {
      "numerator": "1",
      "denominator": "31250000",
      "decimal_display": "3.2E-8"
    },
    "strict_comparison_integer_margin": "32000000000000000000",
    "exact_lower_bound_strictly_above_threshold": true,
    "all_depths_live_mass_equals_recurrence": true,
    "all_depths_survivor_plus_Fraction_deleted_mass_equals_one": true,
    "all_depths_total_live_node_count_checked": true
  },
  {
    "parameters": {
      "a": 18,
      "b": 1,
      "d": 3,
      "D": 20,
      "N": 73
    },
    "r_last_deleted": 4,
    "r_min_after_deletion": 4,
    "max_weight_live_node_count": "2912",
    "R_N": "417151036299542523840249867567301854593852620224891335670636945315466717808858320937588621312",
    "H_N": "410963122147519885718066723155689209764147116520545174410510008329199685768993065402368",
    "D_power_N": "94447329657392904273920000000000000000000000000000000000000000000000000000000000000000000000000",
    "lower_numerator_raw": "834294675262886392322556809933586906781929485801685301528134501450783510023372800000000000000",
    "lower_denominator_raw": "188894659314785808547840000000000000000000000000000000000000000000000000000000000000000000000000",
    "finite_survivor": {
      "numerator": "706681343453974257387800747720942753539468543924566357514974859598050801",
      "denominator": "160000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "0.00441675839658733910867375467325589220962167839952853973446859"
    },
    "t_N": {
      "numerator": "696198609130885597695136021593547814689632716312296141651066450089",
      "denominator": "160000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "4.35124130706803498559460013495967384181020447695185088531917E-9"
    },
    "improved_tail": {
      "numerator": "6265787482177970379256224194341930332206694446810665274859598050801",
      "denominator": "160000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "3.91611717636123148703514012146370645762918402925666579678725E-8"
    },
    "survivor_lower_bound": {
      "numerator": "7066750776664920794174214914967484116091363372301195468497",
      "denominator": "1600000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "0.00441671923541557549635888432185467757255710210768824716781062"
    },
    "strict_threshold": {
      "numerator": "5520899",
      "denominator": "1250000000",
      "decimal_display": "0.0044167192"
    },
    "lower_bound_minus_threshold": {
      "numerator": "56664920794174214914967484116091363372301195468497",
      "denominator": "1600000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "3.5415575496358884321854677572557102107688247167810625E-11"
    },
    "strict_comparison_integer_margin": "8362266334777234704256983633477411857252106626910168126813479387529216000000000000000000000000",
    "exact_lower_bound_strictly_above_threshold": true,
    "all_depths_live_mass_equals_recurrence": true,
    "all_depths_survivor_plus_Fraction_deleted_mass_equals_one": true,
    "all_depths_total_live_node_count_checked": true
  },
  {
    "parameters": {
      "a": 98,
      "b": 1,
      "d": 3,
      "D": 100,
      "N": 729
    },
    "r_last_deleted": 4,
    "r_min_after_deletion": 4,
    "max_weight_live_node_count": "2256",
    "R_N": "20054787877618452439061582522413920620229248020000017973076427542100548460715537029921921862834897200335279778593102574348583734091111213844417625365402608351600173247263686668002626089999064576712589584702770987928387237034749183311251934703951713755097025381119735421498998585952246235421584303109652272274714178734389973974971706603097409577100080792779799252346031955164047968651023406505551341529115820044816184239473933485011761173389422824051435449015696302566229536587557274102652288817592607359074665208496491945175703583402082976974873753302823634014154598494116883652680870645691438260567754096482508045202150465599258682302179487625192206751196384626803596398360753662034814171953696562774191459934909720126375405538780816154791870939268139851615000428527069939211223073563590301713854414214852300458723706934908809151122997281447634990868272940885198532105168780525068570293655102263142904409225320141860580639787673154038564564245413744454729876154076287987666688125581824125060006610250528648054976270462877935446869544313059370876105402573391850304353768311498461418580338699001670601675694276740383055215672061591338894552339929011185548108255212491024338157998002929675550911786320015894694845335659747549858439444930149159709673780079811264809320059087677633372331203665799327619943136747703221780419364192324200626199176522591961113569017056950106324175493567966113785070958152366115279494163938503613986096697121619701245036390776832",
    "H_N": "4354164945464051029492606635258653022791197543171689833449674031414001895598882964122237548243712984469051072945889463961043085996824849497253114456155105576474769115673522981428552338300256930300056550774048719123158146598188814993958198239899939293492239498397938746652086657865746618430809230046422738341518162734183096053124436930144899608015914270456041468472735672829612722581745945745492159592751350698764774152755342064763049445388804805081952985766657745644644026002094944669746787905287238065479520243779095991498001693407650484761282114979880706091716671094952670829503906903276892940744540980514329601338760381271473050767861065443901967033200073395884913340041526819835789725770901866529283871839313783786505730941934527978352411017379897967929123876310433123950277353096201110494180659193035177692549159370431081577172400714099352508997657112900105485316838134087625614331900875600188271839629807768158932105184460501311130892743974079105185230367095238533175139267858367481841847523429693393274752610927487133557409374915838885766803915312333750373704050233032251810183707563299503964831436388881952491052884467235762039367575215267515412499816823227714244957748480630852782041140708058068074688725507315090712860186932850485307751250302231021614034237415761861299302027094284553811177616771028966616169881645432636255563101247215694225652042986207663134040124771123897105150328883254982937520481918083606063706524515204824301568",
    "D_power_N": "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "lower_numerator_raw": "40109575328528740222646164154552390985110499806462676715327251406133041842858888291153313241690514672786687079219200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "lower_denominator_raw": "2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "finite_survivor": {
      "numerator": "113624298864540003980583487188992032760200145839487429049608707827559488193523597380534559117812857736162705102368685985335256832021559118566037125464747851883326056458802735590180485355701240977673928438048145425631781917035479297103483949598615432118400187538764896530640469975720109002520611256799771963518724137277643148678645513075539782616435944985911856125403344423602726799120068666005704662681148674495346073002975211345475965044227068873468541288434088752846083723450545324632520442094372507811171709482205334934774215855884735049111905466540720666339163526858973942391041428157721236029159650290619377846681067039364697938530741003791976801346299940296984985688416265913459017386229037499927657916856603117281213233047816970495259748229367460171237736685937247458310257147350957126283414464036546830722850708284547944252345617547725983941562151248580336103848952519199452779889251006673099113309271842357827195616714317615236055086096037549362756384469870295621898529340206362776492011475115940048672307110789072487406357532863006066959832761988557875745912669186480882221370351147353055541328974715544367619055953873569779327906081623417808300086766663842908789354563447499356922435475728044678731078059152101510034514151201",
      "denominator": "5665694374725698898777581470713326660587999839703795410519081525700850037567234645954374960221713373668821541974837150200540609490241478394104911636866712505185148361419840433932416723325238467282581681773186349196380854245912600015179858874758058739510179825235481922032542290708577687601301021256197749033518240184015778592398538906838164937174737640595217531676681677289773502861463995333026050805776919409044274777348864684033665578687417836735016035851182576764742404584751511720241978764533996582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "0.0000200547878776184524390615825224139206202292480200000179730764"
    },
    "t_N": {
      "numerator": "24669367838143503443064379400720919172265950523164853071023736965204550637982935379873596135330090639886635774802708911370453128377972932635322775152456359809266792404435907544298899708963124234981637477087397412552660833866105814445931889636643232805851215151466512112210428413543567910001789026952384493579009678652828549769851051255885519903350047095009796438113964478008941102913780153300616329301766437351749067868964598752680331061319975762896166242859567025350821708105682405112391330176932371141747823666047243272517692174942743887626071904891408311772632121273286559758320841551615503067155497507075123817129891794663892673546775036762169386536673162973232985018642020762984266071427095059527685777903698229245873815724393056086313621636147708911957903009353270554027570553597620703347684629198425524658868325392905012603014815998807390841807761961303039847330601077140596959319859165577740241680771983584014577910515021532369306888762505232336119801951467316925310333934214122683165631429564740961444674948722578725160469511570608831877317507668283932024213895555538170431578633786557734177868252400388897017827954680161348604559547108165036054364140995701113539744884835151744402613156708797511411267377755806411249",
      "denominator": "5665694374725698898777581470713326660587999839703795410519081525700850037567234645954374960221713373668821541974837150200540609490241478394104911636866712505185148361419840433932416723325238467282581681773186349196380854245912600015179858874758058739510179825235481922032542290708577687601301021256197749033518240184015778592398538906838164937174737640595217531676681677289773502861463995333026050805776919409044274777348864684033665578687417836735016035851182576764742404584751511720241978764533996582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "4.35416494546405102949260663525865302279119754317168983344967E-15"
    },
    "improved_tail": {
      "numerator": "1208799024069031668710154590635325039441031575635077800480163111295022981261163833613806210631174441354445152965332736657152203290520673699130815982470361630654072827817359469670646085739193087514100236377282473215080380859439184907850662592195518407486709542421859093498310992263634827590087662320666840185371474253988598938722701511538390475264152307655480025467584259422438114042775227511730200135786555430235704325579265338881336222004678812381912145900118784242190263697178437850507175178669686185945643359636314920353366916572194450493677523339679007276858973942391041428157721236029159650290619377846681067039364697938530741003791976801346299940296984985688416265913459017386229037499927657916856603117281213233047816970495259748229367460171237736685937247458310257147350957126283414464036546830722850708284547944252345617547725983941562151248580336103848952519199452779889251006673099113309271842357827195616714317615236055086096037549362756384469870295621898529340206362776492011475115940048672307110789072487406357532863006066959832761988557875745912669186480882221370351147353055541328974715544367619055953873569779327906081623417808300086766663842908789354563447499356922435475728044678731078059152101510034514151201",
      "denominator": "5665694374725698898777581470713326660587999839703795410519081525700850037567234645954374960221713373668821541974837150200540609490241478394104911636866712505185148361419840433932416723325238467282581681773186349196380854245912600015179858874758058739510179825235481922032542290708577687601301021256197749033518240184015778592398538906838164937174737640595217531676681677289773502861463995333026050805776919409044274777348864684033665578687417836735016035851182576764742404584751511720241978764533996582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "2.13354082327738500445137725127673998116768679615412801839034E-13"
    },
    "survivor_lower_bound": {
      "numerator": "5566321754708716848892591810081863360636159039138520331819644433054150834247321184993411330678497",
      "denominator": "277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "0.0000200547876642643701113230820772761954925552499032313383576636"
    },
    "strict_threshold": {
      "numerator": "1002739383",
      "denominator": "50000000000000",
      "decimal_display": "0.00002005478766"
    },
    "lower_bound_minus_threshold": {
      "numerator": "1183600470778556922678613620035573101638520331819644433054150834247321184993411330678497",
      "denominator": "277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000",
      "decimal_display": "4.26437011132308207727619549255524990323133835766362570306652E-15"
    },
    "strict_comparison_integer_margin": "426437011132308207727619549255524990323133835766362570306652092142944414557665662084525733639334353960960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "exact_lower_bound_strictly_above_threshold": true,
    "all_depths_live_mass_equals_recurrence": true,
    "all_depths_survivor_plus_Fraction_deleted_mass_equals_one": true,
    "all_depths_total_live_node_count_checked": true
  }
]
''')
OLD = json.loads(r'''
[
  {
    "a": 8,
    "N": 22,
    "R_N": "313976780752303423488",
    "old_numerator": "37657751145901195264",
    "old_denominator": "20000000000000000000000",
    "target_denominator": 1000,
    "old_margin": "17657751145901195264000"
  },
  {
    "a": 18,
    "N": 73,
    "R_N": "417151036299542523840249867567301854593852620224891335670636945315466717808858320937588621312",
    "old_numerator": "57759307809040192263983833194754360472085301780289167220755315212344243778571953268955545600",
    "old_denominator": "188894659314785808547840000000000000000000000000000000000000000000000000000000000000000000000000",
    "target_denominator": 10000,
    "old_margin": "388698418775616114091998331947543604720853017802891672207553152123442437785719532689555456000000"
  },
  {
    "a": 98,
    "N": 729,
    "R_N": "20054787877618452439061582522413920620229248020000017973076427542100548460715537029921921862834897200335279778593102574348583734091111213844417625365402608351600173247263686668002626089999064576712589584702770987928387237034749183311251934703951713755097025381119735421498998585952246235421584303109652272274714178734389973974971706603097409577100080792779799252346031955164047968651023406505551341529115820044816184239473933485011761173389422824051435449015696302566229536587557274102652288817592607359074665208496491945175703583402082976974873753302823634014154598494116883652680870645691438260567754096482508045202150465599258682302179487625192206751196384626803596398360753662034814171953696562774191459934909720126375405538780816154791870939268139851615000428527069939211223073563590301713854414214852300458723706934908809151122997281447634990868272940885198532105168780525068570293655102263142904409225320141860580639787673154038564564245413744454729876154076287987666688125581824125060006610250528648054976270462877935446869544313059370876105402573391850304353768311498461418580338699001670601675694276740383055215672061591338894552339929011185548108255212491024338157998002929675550911786320015894694845335659747549858439444930149159709673780079811264809320059087677633372331203665799327619943136747703221780419364192324200626199176522591961113569017056950106324175493567966113785070958152366115279494163938503613986096697121619701245036390776832",
    "old_numerator": "751373286211969354774992150308155095897017607500473211609968652440968679966547038650655953596439585552852849214771873213257963648414025412864104425911999732448380153170950715645165860929415132609687364798164226338529382015037935760639052018876320725742708942156499689484522130297945763254342157295735118236398275665231440135631651611715583222862632641248441469134890825728819508986955328876754253985905995810595454199641329823651793768042380396009394576088029321972475496813378739654010283859306783067953945288607676972165810003676238619936503634983617429834597724828302300560428856524152180540874501509397355219804714625566700193006240714172896296085017345275339465722428644643324257403146522031070807640206003470197538997069562901673341696698224919508498055855049826342879967461210050054918262596220528572614661198256915122115011223118319512838764132013511887973293867294839019277317496813214887199705518863735470645504020956834844280315708543609076407107857989730811396025041628606612783089770874306087823851127001210303024124081448968556124675063961939255555398908082699535473565684448044600593999476970213874541908662137561742628301364291336930527985359397921646594866812116401052967762326247944138642277924594007689458550288066906731672855526265733470868281618701996921297500691182389829170564792515470976965149936573636764803866683924561081167972497157493389944475639273074920542054929625393247014449141559865972750964262231812617511299281059840",
    "old_denominator": "2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "target_denominator": 10000000,
    "old_margin": "5513732862119693547749921503081550958970176075004732116099686524409686799665470386506559535964395855528528492147718732132579636484140254128641044259119997324483801531709507156451658609294151326096873647981642263385293820150379357606390520188763207257427089421564996894845221302979457632543421572957351182363982756652314401356316516117155832228626326412484414691348908257288195089869553288767542539859059958105954541996413298236517937680423803960093945760880293219724754968133787396540102838593067830679539452886076769721658100036762386199365036349836174298345977248283023005604288565241521805408745015093973552198047146255667001930062407141728962960850173452753394657224286446433242574031465220310708076402060034701975389970695629016733416966982249195084980558550498263428799674612100500549182625962205285726146611982569151221150112231183195128387641320135118879732938672948390192773174968132148871997055188637354706455040209568348442803157085436090764071078579897308113960250416286066127830897708743060878238511270012103030241240814489685561246750639619392555553989080826995354735656844480446005939994769702138745419086621375617426283013642913369305279853593979216465948668121164010529677623262479441386422779245940076894585502880669067316728555262657334708682816187019969212975006911823898291705647925154709769651499365736367648038666839245610811679724971574933899444756392730749205420549296253932470144491415598659727509642622318126175112992810598400000000"
  }
]
''')

if __name__ == "__main__":
    for expected, old in zip(EXPECTED, OLD):
        pars = expected["parameters"]
        a, b, d, D, N = (pars[k] for k in ("a", "b", "d", "D", "N"))
        target = expected["strict_threshold"]
        result = certify(a, b, d, N,
                         target["numerator"] + "/" + target["denominator"])
        assert result == expected
        counts, R = [1], 1
        for n in range(1, N + 1):
            expanded = [0] * (n + 1)
            for k, count in enumerate(counts):
                expanded[k] += count
                expanded[k + 1] += (d - 1) * count
            k = next(k for k, count in enumerate(expanded) if count)
            expanded[k] -= 1
            R = D * R - a ** (n-k) * b ** k
            counts = expanded
        assert R == int(expected["R_N"]) == int(old["R_N"])
        num, den = (D-a)*R-a**(N+1), (D-a)*D**N
        margin = old["target_denominator"]*num-den
        assert (str(num), str(den), str(margin)) == (
            old["old_numerator"], old["old_denominator"], old["old_margin"])
        assert margin > 0
        assert D**D < 2**D * a**a * b**((d-1)*b)
    assert Fraction(EXPECTED[0]["survivor_lower_bound"]["numerator"] + "/" +
                    EXPECTED[0]["survivor_lower_bound"]["denominator"]) == Fraction(61211,1953125)
    print("THREE_CASE_CERTIFICATES_OK")
```

**有限见证 6.6.4（分配 Bellman、显式树与压缩计数）。** 下列程序保存分配见证、极端行和逐节点重标号；逐词检查前缀自由、预算、直接柱质量与重标后 iid 质量，并与显式树贪心及压缩贪心分别比较。有限域为：$d=2,3$、深度四、每层预算 $\{0,1,2\}$；$d=4$、深度三、同一预算集合；各自三个有理 $\delta$ 见程序。另包括零预算、首层耗尽和四个深度七一词见证。总计 589 次执行、577 个不同输入（控制例与主域有重复）；这是有限核对域，不能据此替代定理 6.1.4。

四个深度七值依次为 $(d,\delta)=(3,1/4),(3,1/10),(4,1/5),(2,1/3)$ 时的 $367/512,75226/78125,41312/78125,2186/2187$。代码中的精确数据还保留全部贪心词、Bellman 词、重标词、逐层质量及选中计数，因而不仅是一个最优值断言。

```python
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json

@lru_cache(None)
def compositions(n, d):
    if d == 1:
        return ((n,),)
    return tuple((k,) + rest for k in range(n + 1) for rest in compositions(n-k, d-1))

@lru_cache(None)
def allocations(b, d):
    # Canonical child order is permitted because the Bellman operator is symmetric.
    out = set()
    for columns in product(*(compositions(n, d) for n in b)):
        rows = tuple(sorted(tuple(col[i] for col in columns) for i in range(d)))
        out.add(rows)
    return tuple(sorted(out))

class Optimizer:
    def __init__(self, d, delta):
        self.d = d
        self.delta = delta
        self.u = delta.numerator
        self.v = delta.denominator
        self.r = 1 - (d-1)*delta
        self.solve = lru_cache(None)(self._solve)

    def _solve(self, b):
        # Budget b[j] is the at-most count at relative depth j, including root j=0.
        height = len(b)-1
        if b[0]:
            return self.v**height, True
        if height == 0 or not any(b):
            return 0, None
        best_value, best_tree = -1, None
        for parts in allocations(b[1:], self.d):
            child_results = tuple(self.solve(part) for part in parts)
            vals = tuple(x[0] for x in child_results)
            value = self.u*sum(vals) + (self.v-self.d*self.u)*max(vals)
            if value > best_value:
                best_value = value
                best_tree = tuple(x[1] for x in child_results)
        return best_value, best_tree

    def history_value(self, b):
        numerator, tree = self.solve((0,)+tuple(b))
        return Fraction(numerator, self.v**len(b)), tree

    def direct_check(self, tree, b):
        # Independently evaluate recursively with Fraction and return explicit F/rows.
        def walk(t, h):
            if t is True:
                return Fraction(1), [h], {}
            if t is None:
                return Fraction(0), [], {}
            children = [walk(child, h+str(a)) for a, child in enumerate(t)]
            heavy = max(range(self.d), key=lambda a: children[a][0])
            row = [self.delta]*self.d
            row[heavy] = self.r
            value = sum(row[a]*children[a][0] for a in range(self.d))
            words = [word for child in children for word in child[1]]
            rows = {h: row}
            for child in children:
                rows.update(child[2])
            return value, words, rows
        val, words, rows = walk(tree, '')
        assert all(len([w for w in words if len(w)==n]) <= cap for n, cap in enumerate(b, 1))
        assert all(not v.startswith(u) for u in words for v in words if u != v)
        cylinder_sum = Fraction(0)
        renamed_words = []
        for w in words:
            p = Fraction(1)
            renamed = ''
            for i, a in enumerate(w):
                row = rows[w[:i]]
                p *= row[int(a)]
                # Consistent deterministic node permutation: first maximal-probability
                # child is assigned 0, others in increasing original-label order.
                heavy = max(range(self.d), key=lambda j: row[j])
                labels = [heavy] + [j for j in range(self.d) if j != heavy]
                renamed += str(labels.index(int(a)))
            renamed_words.append(renamed)
            cylinder_sum += p
            iid_mass = self.r**renamed.count('0') * self.delta**(len(renamed)-renamed.count('0'))
            assert iid_mass == p
        assert cylinder_sum == val
        assert all(not v.startswith(u) for u in renamed_words for v in renamed_words if u != v)
        return val, words, renamed_words

    def compressed_greedy(self, b):
        # Counts indexed by number of low-probability letters in an active word.
        active = [1]
        masses = []
        selected_counts = []
        for n, cap in enumerate(b, 1):
            candidates = [(active[k] if k < len(active) else 0)
                          + (self.d-1)*(active[k-1] if k > 0 else 0)
                          for k in range(n+1)]
            chosen = []
            remaining = cap
            for available in candidates:
                take = min(available, remaining)
                chosen.append(take)
                remaining -= take
            active = [available-take for available,take in zip(candidates,chosen)]
            mass = sum(chosen[k]*self.r**(n-k)*self.delta**k for k in range(n+1))
            masses.append(mass)
            selected_counts.append(chosen)
        return sum(masses), masses, selected_counts

    def greedy(self, b):
        active = [('', Fraction(1))]
        selected = []
        masses = []
        p = [self.r]+[self.delta]*(self.d-1)
        for cap in b:
            children = [(h+str(a), mass*p[a]) for h,mass in active for a in range(self.d)]
            children.sort(key=lambda x: (-x[1], x[0]))
            chosen = children[:cap]
            active = children[cap:]
            selected.extend(h for h,_ in chosen)
            masses.append(sum(mass for _,mass in chosen))
        return sum(masses), selected, masses

EXPECTED = json.loads(r'''
{
  "arithmetic": "exact integers and fractions.Fraction; explicit-tree greedy also checked against count compression",
  "total_instances": 589,
  "suites": [
    {
      "d": 2,
      "delta": "1/5",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 201,
      "exact_agreement": true
    },
    {
      "d": 2,
      "delta": "1/3",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 201,
      "exact_agreement": true
    },
    {
      "d": 2,
      "delta": "1/2",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 201,
      "exact_agreement": true
    },
    {
      "d": 3,
      "delta": "1/10",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 203,
      "exact_agreement": true
    },
    {
      "d": 3,
      "delta": "1/4",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 203,
      "exact_agreement": true
    },
    {
      "d": 3,
      "delta": "1/3",
      "depth": 4,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 83,
      "optimizer_states": 203,
      "exact_agreement": true
    },
    {
      "d": 4,
      "delta": "1/10",
      "depth": 3,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 29,
      "optimizer_states": 69,
      "exact_agreement": true
    },
    {
      "d": 4,
      "delta": "1/5",
      "depth": 3,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 29,
      "optimizer_states": 69,
      "exact_agreement": true
    },
    {
      "d": 4,
      "delta": "1/4",
      "depth": 3,
      "budget_alphabet": [
        0,
        1,
        2
      ],
      "instances": 29,
      "optimizer_states": 69,
      "exact_agreement": true
    }
  ],
  "one_per_depth_examples": [
    {
      "d": 3,
      "delta": "1/4",
      "depth": 7,
      "budgets": [
        1,
        1,
        1,
        1,
        1,
        1,
        1
      ],
      "joint_optimum": "367/512",
      "greedy_words": [
        "0",
        "10",
        "200",
        "1100",
        "12000",
        "201000",
        "2020000"
      ],
      "greedy_depth_masses": [
        "1/2",
        "1/8",
        "1/16",
        "1/64",
        "1/128",
        "1/256",
        "1/512"
      ],
      "compressed_chosen_counts": [
        [
          1,
          0
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0,
          0
        ]
      ],
      "bellman_witness_words": [
        "0202222",
        "021222",
        "022",
        "10222",
        "1122",
        "12",
        "2"
      ],
      "renamed_witness_words": [
        "1010000",
        "102000",
        "100",
        "21000",
        "2200",
        "20",
        "0"
      ]
    },
    {
      "d": 3,
      "delta": "1/10",
      "depth": 7,
      "budgets": [
        1,
        1,
        1,
        1,
        1,
        1,
        1
      ],
      "joint_optimum": "75226/78125",
      "greedy_words": [
        "0",
        "10",
        "200",
        "1100",
        "12000",
        "201000",
        "2020000"
      ],
      "greedy_depth_masses": [
        "4/5",
        "2/25",
        "8/125",
        "4/625",
        "16/3125",
        "64/15625",
        "256/78125"
      ],
      "compressed_chosen_counts": [
        [
          1,
          0
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0,
          0
        ]
      ],
      "bellman_witness_words": [
        "0202222",
        "021222",
        "022",
        "10222",
        "1122",
        "12",
        "2"
      ],
      "renamed_witness_words": [
        "1010000",
        "102000",
        "100",
        "21000",
        "2200",
        "20",
        "0"
      ]
    },
    {
      "d": 4,
      "delta": "1/5",
      "depth": 7,
      "budgets": [
        1,
        1,
        1,
        1,
        1,
        1,
        1
      ],
      "joint_optimum": "41312/78125",
      "greedy_words": [
        "0",
        "10",
        "200",
        "3000",
        "11000",
        "120000",
        "1300000"
      ],
      "greedy_depth_masses": [
        "2/5",
        "2/25",
        "4/125",
        "8/625",
        "8/3125",
        "16/15625",
        "32/78125"
      ],
      "compressed_chosen_counts": [
        [
          1,
          0
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          1,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0,
          0,
          0,
          0,
          0
        ]
      ],
      "bellman_witness_words": [
        "0333",
        "133",
        "2033333",
        "213333",
        "22333",
        "23",
        "3"
      ],
      "renamed_witness_words": [
        "1000",
        "200",
        "3100000",
        "320000",
        "33000",
        "30",
        "0"
      ]
    },
    {
      "d": 2,
      "delta": "1/3",
      "depth": 7,
      "budgets": [
        1,
        1,
        1,
        1,
        1,
        1,
        1
      ],
      "joint_optimum": "2186/2187",
      "greedy_words": [
        "0",
        "10",
        "110",
        "1110",
        "11110",
        "111110",
        "1111110"
      ],
      "greedy_depth_masses": [
        "2/3",
        "2/9",
        "2/27",
        "2/81",
        "2/243",
        "2/729",
        "2/2187"
      ],
      "compressed_chosen_counts": [
        [
          1,
          0
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0,
          0,
          0,
          1,
          0
        ]
      ],
      "bellman_witness_words": [
        "0000001",
        "000001",
        "00001",
        "0001",
        "001",
        "01",
        "1"
      ],
      "renamed_witness_words": [
        "1111110",
        "111110",
        "11110",
        "1110",
        "110",
        "10",
        "0"
      ]
    }
  ],
  "interpretation": "Finite arithmetic validation only; general and infinite conclusions require the separate mathematical proof."
}
''')

def main():
    suites = [(2, 4, 2, [Fraction(1,5), Fraction(1,3), Fraction(1,2)]),
              (3, 4, 2, [Fraction(1,10), Fraction(1,4), Fraction(1,3)]),
              (4, 3, 2, [Fraction(1,10), Fraction(1,5), Fraction(1,4)])]
    results = []
    checked = 0
    for d,N,cap,deltas in suites:
        for delta in deltas:
            opt = Optimizer(d,delta)
            count = 0
            for b in product(range(cap+1), repeat=N):
                history, tree = opt.history_value(b)
                greedy, words, masses = opt.greedy(b)
                direct, _, _ = opt.direct_check(tree,b)
                compressed, compressed_masses, _ = opt.compressed_greedy(b)
                assert history == direct
                assert compressed == greedy and compressed_masses == masses
                if history != greedy:
                    raise AssertionError({'d':d,'delta':str(delta),'b':b,'history':str(history),'greedy':str(greedy)})
                count += 1
            # Full first-level extinction and otherwise zero are separate controls.
            for b in [(d,)+(0,)*(N-1), (0,)*N]:
                history, tree = opt.history_value(b)
                greedy, _, _ = opt.greedy(b)
                direct, _, _ = opt.direct_check(tree,b)
                assert history == direct == greedy
                count += 1
            checked += count
            results.append({'d':d,'delta':str(delta),'depth':N,'budget_alphabet':list(range(cap+1)),
                            'instances':count,'optimizer_states':opt.solve.cache_info().currsize,
                            'exact_agreement':True})
    illustrative = []
    for d,delta,N in [(3,Fraction(1,4),7),(3,Fraction(1,10),7),(4,Fraction(1,5),7),(2,Fraction(1,3),7)]:
        opt = Optimizer(d,delta)
        b = (1,)*N
        history,tree = opt.history_value(b)
        greedy,words,masses = opt.greedy(b)
        direct,fw,renamed = opt.direct_check(tree,b)
        compressed, compressed_masses, compressed_counts = opt.compressed_greedy(b)
        assert history == greedy == direct == compressed
        assert masses == compressed_masses
        checked += 1
        illustrative.append({'d':d,'delta':str(delta),'depth':N,'budgets':list(b),
                            'joint_optimum':str(history),'greedy_words':words,
                            'greedy_depth_masses':[str(x) for x in masses],
                            'compressed_chosen_counts':compressed_counts,
                            'bellman_witness_words':fw,'renamed_witness_words':renamed})
    out = {'arithmetic':'exact integers and fractions.Fraction; explicit-tree greedy also checked against count compression','total_instances':checked,
           'suites':results,'one_per_depth_examples':illustrative,
           'interpretation':'Finite arithmetic validation only; general and infinite conclusions require the separate mathematical proof.'}
    assert out == EXPECTED
    print(json.dumps(out,indent=2))

if __name__ == '__main__':
    main()
```

**构造 6.6.5（保留多步有理运输证书）。** 输入 $d$、有理 $0<\delta\le1/d$、预算程序和有效次指数模量 $\nu_{\rm bud}$，并承诺 $B<1$。置 $r=1-(d-1)\delta$，选有理 $a,c>1$ 使 $\rho=ar<1$、$c\rho<1$，选整数 $J$ 使 $1+1/(J\delta)<c$。因 $a<1/r\le d$，对 $N\ge\nu_{\rm bud}(a)$，
$$
B\le B_N+\frac{(a/d)^{N+1}}{1-a/d}.
$$
右边趋 $B<1$，故搜索其小于一并取一减该上界，得有理 $0<\gamma_0\le1-B$。

对任意允许历史律，使用第 6.2.3 节的 $q_j=(1-j/J)u+(j/J)q$。相邻行差至多 $1/J$ 且每坐标至少 $\delta$，给反向比 $q_{j-1}(a\mid v)\le c q_j(a\mid v)$。在同一有限剩余 clopen 上比较并补实际原律尾，得 $N\ge\nu_{\rm bud}(a)$ 时
$$
\mu_{q_{j-1}}(E_F)\le c^N\mu_{q_j}(E_F)+\frac{\rho}{1-\rho}(c\rho)^N.
$$
若上一层证书为 $\gamma_{j-1}>0$，搜索 $N_j\ge\max(1,\nu_{\rm bud}(a))$ 使 $\rho(c\rho)^{N_j}/(1-\rho)<\gamma_{j-1}/2$，置 $\gamma_j=\gamma_{j-1}/(2c^{N_j})$。$c\rho<1$ 保证每步终止，有限 $J$ 次后 $0<\gamma_J\le\Gamma$。算法不读取实际 $q$，中间律仅用于证明，目标仍是原律。

第 5.3.2 节的一词坐标算法也完整保留：其输入限定 $d\ge3$、$0<\ell<\min(1/d,\min p)$；代入 $r=1-(d-1)\ell,c=1+\ell$ 有 $rc=1-(d-2)\ell-(d-1)\ell^2<1$，取 $J>\ell^{-2}$，$q_j=(1-j/J)u+(j/J)p$。该节的运输余项是 $r(rc)^N/(1-r)$，不是上面一般预算的 $\rho$ 项；初始 $\gamma_0=(d-2)/(d-1)$，搜索余项小于 $\gamma_{j-1}/2$ 后同样置 $\gamma_j=\gamma_{j-1}/(2c^{N_j})$，输出 $\gamma_J/2$。这些替换说明一般历史构造与既有 iid 构造各自的常数和前提，没有另立新的坐标算法所有者。迭代长度、截断深度和有理位数可很大，未声称快速运行。

**证书 6.6.6（不可和最大字母尾下的四个检查点）。** 固定
$$
d=3,\quad\delta=1/8,\quad p^*=(6,1,1)/8,\quad
b_n=0\ (n<3),\qquad b_n=3^n\mathbin{//}2^n\ (n\ge3).
$$
于是 $B\le\sum_{n\ge3}2^{-n}=1/4$。$s=2$ 时 $Z_2=19/32,C=1,e^{\beta_0}=3/2$，$\rho=\sqrt{57}/8<19/20$ 的严格性由 $57\cdot400=22800<23104=361\cdot64$ 承担。定理 6.2.4 的辅助尾在 $N=12$ 为 $2^{-6}\rho/(1-\rho)<19/64$，所以仍有原解析证书
$$
\Gamma>\frac{29}{64}\left(\frac38\right)^{12}
=\frac{15411789}{4398046511104}>0.
$$
另一方面 $b_nr^n\ge(9/8)^n-(3/4)^n\to\infty$，故 $W_N$ 发散，不能用最大字母可和性解释这个证书。

原律尾独立地满足 $T_N=19(19/20)^N=19^{N+1}/20^N$。记有限联合最优幸存 $Q_N=1-M_N(p^*,b)$，把有限码空层延长及把任意无限码截断分别给
$$
M_N\le1-\Gamma\le M_N+T_N,\qquad
\max(0,Q_N-T_N)\le\Gamma\le Q_N.
$$
下列四个完整有理记录保留 $N=12,64,128,256$ 的 $Q_N,T_N,\max(0,Q_N-T_N)$；前两个截断下界为零，不使上面的 $N=12$ 辅助头正界失效。每个数字都是整数递推的结果，显示用近似区间不参加不等式判定。

在最后一层，$Q_{256}=P/2^{542}$，其中 $P$ 为下方记录的完整分子，整数证书为
$$
49677\,2^{542}<10^6P<49678\,2^{542},\qquad
500000\,19^{256}<20^{256}.
$$
第二式给 $T_{256}<38/10^6$，合成
$$
\frac{49639}{10^6}<\Gamma<\frac{49678}{10^6},
\qquad 0.04963<\Gamma<0.0497.
$$
这是类最优间隙区间。每份合法库存都满足其下侧；上侧只约束最优值及其极端实现，空库存的实际幸存量为一。定理 6.1.4 保证同一 $p^*,G$ 达到 $\Gamma$。

下面程序保留原稀有数算法，并独立用反向的重字母数递推 $\widetilde c_{n,k}=2c_{n-1,k}+c_{n-1,k-1}$，由最大 $k$ 开始删。两方向在检查点对照；每层检查实际活数和质量守恒，反向递推另检验整数守恒 $D_n+\sum_ka_n(k)6^{n-k}=8^n$，其中 $D_n$ 是累计删除在分母 $8^n$ 下的分子。它只检验有限算术，无限尾由定理 6.2.4 证明。

```python
from fractions import Fraction as F
import json

def certificate():
    assert F(57, 64) < F(19, 20) ** 2
    assert 1 - F(1, 4) - F(19, 64) == F(29, 64)
    eta = F(29, 64) * F(3, 8) ** 12
    assert eta > 0
    active = [1]
    live_count = 1
    mass = F(0)
    rows = []
    for n in range(1, 257):
        budget = 0 if n < 3 else 3**n // 2**n
        if n >= 3:
            assert F(budget) >= F(3, 2) ** n / 2
        counts = [
            (active[k] if k < len(active) else 0)
            + (2 * active[k - 1] if k > 0 else 0)
            for k in range(n + 1)
        ]
        remaining = budget
        for k in range(n + 1):
            chosen = min(remaining, counts[k])
            remaining -= chosen
            counts[k] -= chosen
            mass += chosen * F(3, 4) ** (n - k) * F(1, 8) ** k
        active = counts
        live_count = max(0, 3*live_count-budget)
        assert sum(active) == live_count
        assert mass + sum(active[k]*F(6**(n-k),8**n) for k in range(n+1)) == 1
        if n in (12, 64, 128, 256):
            upper = 1 - mass
            tail = 19 * F(19, 20) ** n
            lower = max(F(0), upper - tail)
            assert eta <= upper
            rows.append({
                "N": n,
                "finite_gap": str(upper),
                "renyi_tail_upper": str(tail),
                "certified_lower": str(lower),
                "approx_interval": [float(lower), float(upper)],
            })
    assert F(rows[-1]["certified_lower"]) > F(4963, 100000)
    assert F(rows[-1]["finite_gap"]) < F(497, 10000)
    return {
        "exact_inequalities": "passed",
        "uniform_lower_bound": str(eta),
        "uniform_lower_decimal": float(eta),
        "weighted_summability": "fails since b_n r^n >= (9/8)^n/2",
        "greedy_recurrence_checks": rows,
        "scope": "ordinary exact rational certificate; finite computation does not replace infinite proof",
    }


EXPECTED = json.loads(r'''
{
  "exact_inequalities": "passed",
  "uniform_lower_bound": "15411789/4398046511104",
  "uniform_lower_decimal": 3.504235110085574e-06,
  "weighted_summability": "fails since b_n r^n >= (9/8)^n/2",
  "greedy_recurrence_checks": [
    {
      "N": 12,
      "finite_gap": "17912887/268435456",
      "renyi_tail_upper": "42052983462257059/4096000000000000",
      "certified_lower": "0",
      "approx_interval": [
        0.0,
        0.06673070415854454
      ]
    },
    {
      "N": 64,
      "finite_gap": "34658293102105144096939331964521674201367/696898287454081973172991196020261297061888",
      "renyi_tail_upper": "131517656596604663956102176642678715072020072327450916777499793705236707816143809299/184467440737095516160000000000000000000000000000000000000000000000000000000000000000",
      "certified_lower": "0",
      "approx_interval": [
        0.0,
        0.049732211609701725
      ]
    },
    {
      "N": 128,
      "finite_gap": "1507931459910621808100130898800229667258520137596387283545227670060044746407758097/30354201441027016733116592294117482916287606860189680019559568902170379456331382784",
      "renyi_tail_upper": "910362841929601593699242915329458527779099306390144333215018898204440341851315851587840460641860627227530174135975712645444059202059862934786573527168118056972572179/34028236692093846346337460743176821145600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "certified_lower": "204495071303241680512818679215094959948977282127589372676515716376962076348470724598679275989740621878430318351002921730449496398528450001522744272984034778015029157848849/8920298079412249256614287309059344602392166400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "approx_interval": [
        0.022924690350338124,
        0.04967784979750737
      ]
    },
    {
      "N": 256,
      "finite_gap": "715184061049080190881732629416829465795070381011439574350222071131358342763266976240749073923130966405108240840093196833274107594659369542891026416779376981754877/14396524142538228424993723224595141948383030778566133225922417832357880258148761185020930195532450742879746914027266864394266451377581759004827248578768524336431104",
      "renyi_tail_upper": "43618973892954777765289478047635207270458669427007039031714300582378622444236349453270422733678918004735120592065946520519662376065260820422543226418305684176790122412321098238462124009215306168579423552472387890298771991863566398064579467000041351731303873119590663372272616831462695543552164600120849225075983739590773229726739/1157920892373161954235709850086879078532699846656405640394575840079131296399360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "certified_lower": "61717665474779289825115655807366235200654073203945105022512928339863136374759038667806035872817830839082332336628698124017346042365677697853015458494772450930208656050210206210303927127353354988321965968223161288459115585494347112208831412170328377883848560901187914108478354850500197505326280535896187958852500523374422599823088085605896189/1243308091024466605388455620367052100251140376993369293601159942232898742531333438832640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "approx_interval": [
        0.049639880831085795,
        0.04967755091215977
      ]
    }
  ],
  "scope": "ordinary exact rational certificate; finite computation does not replace infinite proof"
}
''')

def reverse_certificate():
    live, deleted, live_count = [1], 0, 1
    rows = {}
    for n in range(1,257):
        budget = 0 if n < 3 else 3**n // 2**n
        expanded = [2*(live[k] if k < len(live) else 0)
                    + (live[k-1] if k else 0) for k in range(n+1)]
        remain = budget
        removed = 0
        for k in range(n,-1,-1):
            take = min(expanded[k],remain)
            expanded[k] -= take
            remain -= take
            removed += take*6**k
        deleted = 8*deleted+removed
        live_count = max(0,3*live_count-budget)
        live = expanded
        survivor = sum(count*6**k for k,count in enumerate(live))
        assert deleted+survivor == 8**n
        assert sum(live) == live_count
        if n in (12,64,128,256):
            rows[n] = F(survivor,8**n)
    return rows

if __name__ == "__main__":
    result = certificate()
    assert result == EXPECTED
    reverse = reverse_certificate()
    for row in result["greedy_recurrence_checks"]:
        assert reverse[row["N"]] == F(row["finite_gap"])
    q = reverse[256]
    P = q.numerator
    assert q.denominator == 2**542
    margins = [10**6*P-49677*2**542,
               49678*2**542-10**6*P,
               20**256-500000*19**256]
    assert all(x > 0 for x in margins)
    assert q-19*F(19,20)**256 > F(49639,10**6)
    print(json.dumps({"integer_margins": [str(x) for x in margins],
                      "checkpoints": result["greedy_recurrence_checks"]},indent=2))
    print("EC_CERTIFICATES_OK")
```

### 6.7 有效输入、指定库存与既有概率接口

**算法 6.7.1（最优值、证书与精确选择的区别）。** 第 5.3.1、5.6.1 节的有限最大值算法按以下输入使用：给有限实际字母列表、预算整数程序和同一 oracle 下的模型实数名，枚举各 $n\le N$ 的全部子集选择并检查前缀自由。每个合法有限码的 iid 质量是有限多项式；隐藏模型中改为有限和 $\sum_we_sM_w\mathbf1$，再对有限 $s$ 取最大。将全部候选计算到同一误差后取有理最大值，误差不扩大。因此有限最优值可计算，不必判定精确并列或选出精确 argmax。有理或有效可比较实代数输入可以支持精确贪心；任意可计算实名不供应一般等号判断。临界候选的实数阈值定义同样不自动给枚举器。

若供应原律长词误差 $\epsilon_N\to0$ 的有效上界，则有限码空层延长、无限码截断给 $M_N\le M_b\le M_N+\epsilon_N$，从而计算 Cauchy 名。隐藏模型对应 $H_N=\max_s\max_{F_{\le N}}\sum_we_sM_w\mathbf1$ 及 $H_N\le1-\eta_b\le H_N+\epsilon_N$。有效正发射与 $K$ 名足够，不要求判定转移是否为零；指定初态的质量还需 $\alpha$ 名或直接的实际输出律名。类优化可用第 6.6.1 节，不枚举所有历史行和码。仅有 $M_N\uparrow M_b$ 不给有效双侧误差；它只给删除最优值的下半可计算性与 gap 的上半可计算性。

次指数输入保留第 5.6.1 节的最小供应：从坐标名搜索有理 $m<r'<1$，选 $1<a<1/r'$，只消费这个 $a$ 的有效起点 $N_0$，不必索取整个模量。$N\ge N_0$ 的尾是 $(ar')^{N+1}/(1-ar')$；常数预算尾为 $c(r')^{N+1}/(1-r')$。给有限最优值有理上近似 $U_N$ 后，严格测试 $U_N+\epsilon_N<1$，成功就输出其正补（或其一半）。正 gap 及趋零误差保证终止，不先计算精确 $B$。第 6.6.2 节活前沿可改善误差，但仍需级数的有效上界；空前沿直接给精确零未来误差。

对定理 6.2.2，若有有理 $\delta$ 及有效模量 $\omega(t)$，保证 $N\ge\omega(t)$ 时 $W_N\le2^{-t}$，令 $N=\max(t,\omega(t))$，计算有理
$$
A_t=1-B_N-(dr)^{-N}2^{-t}.
$$
搜索 $A_t>0$ 并输出 $(d\delta)^NA_t/2$；因 $A_t\ge1-B-2^{-t}$，$B<1$ 保证终止。不读取 $q,F$。数学可和性不等于给出了 $\omega$。

熵输入则供应可计算模型、预算、$a>1,C\ge1$ 和最终界起点，承诺 $\log a<H(p)$ 或 $H(p^*)$ 及 $B<1$。先有效吸收早期预算，取得全深度包络。有限正向量的 $H_s$ 可计算，交错枚举有理 $s>1$ 及精度，直到严格认证 $\log a<H_s$；有限和趋一极限保证存在合格候选。再交错处理所有 $N$ 及其精度，认证 $1-B_N-R_N>0$，用 $R_N$ 的有理上界及 $0<\delta_0<p_{\min}$ 的搜索下界给正证书。不能固定在一个恰为零的括号或不合格 $s$ 上无限等待。原律 $T_N$ 另给最优值 Cauchy 误差，即使 $W_N$ 发散仍可用；对隐藏或历史输入须实际履行相应幂和合同，不能凭一般最终熵率替代。严格正坐标名让下界搜索终止，但不把取得名字的工作抹掉；仅为类 gap 的有理数时，已知 $\delta$ 足够，无需 $K,\alpha$ 可计算。

**边界 6.7.2（四种不同的非统一性）。** 第 5.6.2 节的 HALT-G 仍按其完整停机口径调用：$T(e)$ 是使 $U_e(0)$ 在前 $n-1$ 次转移已停机的最小 $n\ge1$，初始即停取一；任意程序输入对可有效编译为该固定输入口径。只在 $T(e)=n$ 取 $b_n=d^n-1$，其他为零，有限模拟可计算每个预算值。每实例有限支撑、次指数且 $B<1$；均匀律的 gap 为未停机时一、停机时 $d^{-n}$。若算法总能返回正有理 $r_e$ 不超过 gap，搜索 $N$ 使 $d^{-N}<r_e$，有界模拟至深度 $N$。若届时未停而未来 $n>N$ 才停，则 $r_e\le d^{-n}<d^{-N}<r_e$，矛盾，故可决定永不停机，违反停机不可判定性。固定正 iid $p$ 下，选择该层除最轻词之外全部词，gap 恰为 $p_{\min}^n$；同样的有界模拟论证也成立。这个族反驳连“某个正有理下界”都能无尾输入统一提取，不只反驳精确最优值。

HALT-V 改为只在同一首次停机深度取 $b_n=d^{n-1}$。均匀删除最优为 $1/d$ 或零，gap 为 $1-1/d$ 或一。误差小于 $1/(4d)$ 的删除值近似以阈值 $1/(2d)$ 即决定停机；精确 gap 同样不可统一算。有效收敛模量加有限最优值算法也会给这个近似，所以同样不存在。**但共同正有理下界 $1-1/d$ 已知**，不能用 HALT-V 反驳正下界的计算。

另一个非停机参数族固定非均匀 $p$，只在第 $N$ 层取 $b_N=d^{N-1}$。每份 $\beta=0,B=1/d$，有限码不能删掉该层全部正质量词，所以 gap 严格正。选 $h<\gamma<\log d$，最终 $e^{\gamma N}\le d^{N-1}$，低自信息候选质量由强大数律趋一，故该族 gap 趋零。因此仅知道共同的 $p,\beta,B$ 不足以给所有预算一个正常数，尖峰位置有用。均匀律该族的删除恒为 $1/d$，非均匀前提不能删；也不能把 $d^{N-1}$ 误写为 HALT-G 的 $d^N-1$。

第四种对象是指定 c.e. 库存。取均匀三元律和不可判定 c.e. 集 $H$，$F=\{1^e0:e\in H\}$ 前缀自由、每层至多一个，实际幸存质量为 $1-x$，$x=\sum_{e\in H}3^{-(e+1)}$。若 $x$ 可计算，递归决定此前成员位后，令 $a_e=3^{-(e+1)}$ 并减去已知前项。若 $e\notin H$，余量至多 $\sum_{j>e}a_j=a_e/2$；若 $e\in H$，余量至少 $a_e$。把余量近似到误差小于 $a_e/8$，与 $3a_e/4$ 比较即可决定该位，矛盾。因此已知每层一词几何深度尾仍不给库存质量名；浅词可以任意晚公告。

在证书 6.6.6 的固定 $p^*,b$ 中也保留这一障碍：机器停机才公告唯一词 $000$，深度总是三，$b_3=3$ 足够。实际幸存是未停机时一、停机时 $1-(3/4)^3=37/64$。误差小于 $1/10$ 的质量近似以 $3/4$ 为阈值就决定停机，因为 $37/64+1/10<3/4<1-1/10$。这个固定类有有效 $T_N$ 和可计算最优值，仍不供应公告截止或任意实际库存的质量名。

按命题 5.6.3，每个固定可计算次指数预算及固定可计算模型，可把实际存在的有限合格起点写进某个程序，从而该固定最优值可计算；不存在从全部程序统一抽取该常量的算法。这是数学存在、逐实例可计算和统一输入三种量词，不把每个固定的仅数学可和预算都补报为可计算。单向逼近加严格正承诺也不能推翻 HALT-G。

**算法 6.7.3（已知满测后的概率截止）。** 若另有承诺 $M_b=1$，对各有限值交错严格测试 $M_N>1-\varepsilon$，必有一个测试成功；需要实际有限码时，枚举全部有限合法码和它们的质量下近似，直到某个超过 $1-\varepsilon$。这给可用见证，不是精确 argmax。如果输入是指定 c.e. 库存并另承诺其自身删除满测，有限公告并质量趋一，同样的严格搜索给公告阶段和该阶段最大深度。没有这个已知极限承诺，深度截止不等于公告截止。

例 6.4.5 的可判满测码虽然全部合法满测实现的平均长度无穷，仍能搜索这样的 $1-\varepsilon$ 截止；有效高概率截止与有限均值不是同一要求。下面的标准库核对同时保留该例整数预算、固定尖峰有限值、隐藏与历史反例的准确数值。

```python
from fractions import Fraction as F
from itertools import product
from math import isqrt, comb


def hidden_mass(word, emissions, updates, initial):
    alpha = list(initial)
    for a in word:
        alpha = [sum(alpha[s]*emissions[s][a]*updates[s][a][t]
                     for s in range(len(alpha))) for t in range(len(alpha))]
    return sum(alpha)


def deterministic_updates(destinations, d):
    size = len(destinations)
    return [[[F(int(t == destinations[s][a])) for t in range(size)]
             for a in range(d)] for s in range(size)]


def finite_greedy(d, budgets, mass):
    live, chosen = [()], []
    for cap in budgets:
        expanded = [v+(a,) for v in live for a in range(d)]
        expanded.sort(key=lambda w: (-mass(w),w))
        chosen.extend(expanded[:cap])
        live = expanded[cap:]
    return sum((mass(w) for w in chosen),F(0)),chosen


def run():
    rows = {(): (F(3,5),F(2,5)), (0,): (F(99,100),F(1,100)),
            (1,): (F(1,2),F(1,2))}
    def history_mass(w):
        val = F(1)
        for j,a in enumerate(w): val *= rows[w[:j]][a]
        return val
    assert finite_greedy(2,[1,1],history_mass)[0] == F(4,5)
    assert history_mass((1,))+history_mass((0,0)) == F(497,500)
    emission = [[F(2,5),F(7,20),F(1,4)],
                [F(49,50),F(1,100),F(1,100)],
                [F(1,3)]*3,[F(1,3)]*3]
    updates = deterministic_updates([[1,2,3],[1]*3,[2]*3,[3]*3],3)
    mass = lambda w: hidden_mass(w,emission,updates,[F(1),F(0),F(0),F(0)])
    assert finite_greedy(3,[1,1],mass)[0] == F(31,60)
    assert mass((1,))+mass((0,0)) == F(371,500)
    emission = [[F(1,2) if s==a else F(1,4) for a in range(3)] for s in range(3)]
    updates = deterministic_updates([list(range(3))]*3,3)
    markov = lambda w: hidden_mass(w,emission,updates,[F(1,3)]*3)
    assert markov((0,)) == F(1,3) and markov((0,0)) == F(1,6)
    assert sum(markov(w) for w in product(range(3),repeat=3)) == 1
    assert F(9,5)**4-F(256,27) == F(17147,16875)
    assert [isqrt(8**n//n**4) for n in range(2,13)] == [2,2,4,7,14,29,64,143,327,765,1820]
    spike_values = []
    for n in range(1,9):
        weights = sorted((F(1,2)**w.count(0)*F(1,4)**(n-w.count(0))
                          for w in product(range(3),repeat=n)),reverse=True)
        spike_values.append(sum(weights[:3**(n-1)]))
    assert spike_values == [F(1,2),F(1,2),F(9,16),F(19,32),F(79,128),F(341,512),F(687,1024),F(2853,4096)]
    for n in range(1,10):
        count = 0
        for w in product(range(3),repeat=n):
            position, first = 0,None
            for j,a in enumerate(w,1):
                position += 1 if a==0 else -1
                if position == 1 and first is None: first = j
            count += first == n
        expected = 0 if n%2 == 0 else 2**((n-1)//2)*comb(n-1,(n-1)//2)//((n+1)//2)
        assert count == expected
    assert 1-F(3,4)**3 == F(37,64)
    assert F(37,64)+F(1,10)<F(3,4)<1-F(1,10)
    print("RATIONAL_WITNESSES_OK")

if __name__ == "__main__":
    run()
```

**适配 6.7.4（直接消费第 4 章的非 iid 接口）。** 定义 4.2.1 已明确不要求数字独立或柱质量有理。这里取其 $\Sigma_j=A$、参考律为实际 $\mu_q$ 或 $\mu_\alpha$、$K_s=E_s$ 为前 $s$ 个计算步骤所见有限禁柱并的补、$K=E$、$p_s=f_s=\mu(E_s)$、$M=\mu(E)>0$、$\nu_s=\mu(\,\cdot\cap E_s)/f_s$、$\nu=\mu(\,\cdot\cap E)/M$。即使该阶段没有新公告，也必须在有限计算时间结束；阶段与词深度不是同一个索引。

供应实际参考柱的统一可计算名字、完整有限字母列表及同一 c.e. 呈示。正隐藏发射、更新及初态的全部可计算名字可实现矩阵乘积柱名；或直接供应输出律名字即可。非可计算准备的语义 gap 本身不满足这项输入。所有名字和呈示允许相对于同一个 oracle，不能隐去参考律或呈示的 oracle。于是按定义 4.2.1，$\mathbf M$ 是 $M$ 的误差 $2^{-t}$ Cauchy 名，$\mathbf C$ 是每柱条件概率的同精度名，$\mathbf T$ 是所指定同一阶段序列的总变差合格阶段选择器，$\mathbf S$ 使用公平 iid 位、有限输出只读有限输入、字母不可撤回，并以概率一持续输出无限串且律恰为 $\nu$。该 sampler 合同不是正概率成功或允许正概率有限停止；不供应一般逐位等待或平均运行时间。$\mathbf R$ 是全部真实非空切片的特征函数，非法词返回零。

定理 4.2.3–4.2.5 以这些替换直接给
$$
\mathbf M\longleftrightarrow\mathbf T\longrightarrow\mathbf C\longleftrightarrow\mathbf S,
\qquad d_{\rm TV}(\nu_s,\nu)=(f_s-M)/f_s.
$$
无需再建立非 iid 通用接口。仅靠归一化没有反向恢复 $M$；为 $\mathbf C\to\mathbf M$，在定义 4.1.1 中具体取完整标准层分割 $\mathcal D_n=\{[v]:|v|=n\}$，实际权 $w_{n,v}=\mu[v]>0$，以及真实
$$
\mathcal R_n=\{v:E\cap[v]\ne\varnothing\},\quad
A_n=\bigcup_{v\in\mathcal R_n}[v],\quad a_n=\sum_{v\in\mathcal R_n}\mu[v].
$$
命题 4.3.6 的包含在此保持原量词：若 $x\in A_n\setminus E$，同一个深度 $n$ 柱还有幸存者；删掉 $x$ 的任何短禁词也会删掉该幸存者，故其禁词必长于 $n$。按最终不同词预算或其前缀极小族求并集界，得到
$$
0\le a_n-M\le\mu\!\left(\bigcup_{|w|>n,w\in F}[w]\right)\le\epsilon_n,
$$
这里 $\epsilon_n$ 可用已证明有效的原律 $W_n$ 或 $T_n$；辅助头尾 $R_n$ 不充当此处 $\epsilon_n$。不得把真延拓换成“当前没见禁祖先”。

有了有效层选择器，定理 4.1.4 以 $D_n=\max_{|v|=n}\nu[v]/\mu[v]$ 给 $M\le D_n^{-1}\le a_n$；计算所有实际权及条件柱而不查询 $\mathbf R$，就有 $\mathbf C\to\mathbf M$。命题 4.3.1 则以真延拓查询和实际加权和给 $\mathbf R\to\mathbf M$，此方向不需库存枚举。相同层的柱不等权时，不能替换成 $|\mathcal R_n|d^{-n}$。

要加上指向 $\mathbf R$ 的箭头，必须另供全部查询的局部合同，或命题 4.3.3 的独立支撑承诺 $E=\operatorname{supp}\nu$。第 6.3.3 节的移位预算、无最终禁祖先及条件律给有数值下界的查询；所有查询都履约才供应全部 $\mathbf R$。例如一词 iid 的第 5.5.1–5.5.4 节以 $d\ge3$、同一 iid 尾给所有查询；一般预算则逐项使用第 5.5.5 节的 $b^{[h]}$、$B^{[h]}<1$ 和有效移位模量。若从第 5.6.1 节取得 $0<\gamma_h\le\eta_{b^{[h]}}(p)$，再取正坐标下界 $\ell_a<p_a$，严格有理供应可取
$$
g_v=(\gamma_h/2)\prod_{i\le h}\ell_{v_i},
$$
空词用空积一。历史类或隐藏情形可取已取得的严格条件 gap 下界与实际柱正下界相乘，例如 $g_v=\delta_0^h\gamma_h/2$，其中 $0<\delta_0\le\delta$ 且 $\gamma_h$ 不超过对应类 gap。后验加权数值界可替代更粗的最小状态界，但须实际可计算其所用数据。只拿一个查询的供应不能宣布全接口等价。

**适配 6.7.5（原局部化算法的全部精度）。** 不重证引理 4.3.4 和定理 4.3.5，而在其中取 $C=[v]$、$m_C=m_v=\mu(E\cap[v])$、$f_s=\mu(E_s)$、$u_s=\mu(E_s\cap[v])$ 及刚才的有理 $g=g_v>0$，保证空时零、非空时 $m_v>g$。一次质量查询选 $2^{-t}\le g/16$，置 $L=v_M(t)-2^{-t}$，于是 $0\le M-L\le g/8$。其精确局部区间为
$$
\max\{0,L-(f_s-u_s)\}\le m_v\le u_s,
\qquad\text{宽度}\le f_s-L.
$$
按原算法以误差小于 $g/48$ 计算 $f_s$，再加 $g/48$，得 $f_s\le F_s<f_s+g/24$；搜索有理比较 $F_s-L<g/3$。$F_s-L<f_s-M+g/6$ 和 $f_s\downarrow M$ 保证终止。再算 $|u-u_s|<g/12$，空时 $u<5g/12$，非空时 $u>11g/12$，用阈值 $g/2$ 决定。未公告祖先可能晚出现不破坏这个算法，因为它消费最终总质量和同一呈示，而非猜测公告完成。

若已有 $\mathbf C$ 及全部可计算正局部下界，命题 4.3.2 直接给 $\mathbf C\to\mathbf R$；若仅有支撑等号，命题 4.3.3 并行半判定 $\nu[v]>0$ 与某有限 $E_s\cap[v]=\varnothing$，正支撑及紧致有效闭负搜索分别承担终止分支。类 gap 不提供支撑等号；例 6.3.4 正是反例。得到全部这些供应时才有五接口互算。正质量假设是条件律接口的前提，局部质量区间本身仍可在 $M=0$ 使用；二元满测码则不能归一化幸存律。实数请求精度、层枚举数、公告等待、原始词长、采样等待和整数位长分别计成本。

**连接 6.7.6（旧熵证书、回返概率与继续任务）。** 第 5.8.2 节已将定理 4.6.2 的可数 Hölder 具体化为 $f(w)=\widehat p_q(w)$、$g(w)=r_q^{|w|}$，其中 $\widehat p_{q,a}=p_a^q/\sum p_a^q$、$r_q=(\sum p_a^q)^{1/(q-1)}$，正互补指数为 $1/q,(q-1)/q$。前缀柱给第一族可和，一词长度预算和 $r_q<1/2$ 给第二族可和，所得 $1-(r_q/(1-r_q))^{(q-1)/q}$ 数值界原样有效。平方特例和 $q\downarrow1$ 搜索仍归第 4.6.3、4.6.5、4.6.7 节；第 6.2 节的新预算熵界不取代它们。

Perron 代入保留第 4.7.1 节根律：$d=k$、$p_r=\lambda_k^{-(r+1)}$、$\sum_{r<k}p_r=1$、$p(v)=\lambda_k^{-L(v)}$、$L(v)=\sum_i(v_i+1)$。对 $k\ge3$，第 4.7.3–4.7.4 节的 $c_k=(3-\lambda_k)/(1+\lambda_k)$ 和 $\eta_k=1-\sqrt{(3-\lambda_k)/(2(\lambda_k-1))}>1/6$ 仍是所用供应，本章不声称更优统一常数。第 4.7.5 节的原 $1/8$ 算法也不变：$g=2^{-L(v)-3}$、$t=L(v)+7$（或 $g=2^{-kh-3},t=kh+7$），因为 $p(v)\ge2^{-L(v)}$ 及严格 $1/8$ 条件余量给 $m_v>g$，正好 $2^{-t}=g/16$，使用适配 6.7.5 的所有误差。反向按定理 4.7.6 选 $(5/9)^{n+1}/(1-5/9)<2^{-m-1}$，查询全部 $k^n$ 个真延拓并把实际权和近似到另一半误差。它用 $\lambda_k>9/5$，不是对所有一般历史律的精度公式；$k=2$ 保留第 4.7.7–4.7.8 节边界。

第 1.4.2–1.4.4、4.7.9–4.7.11 节已经拥有有锚回返码及有限窗口公式。完整块 $1^r0$ 的质量为 $\lambda_k^{-(r+1)}$，实际时间是屋顶长度的累加；未完成 run 须另计，原始一步是块内倒计时或跨块移动。根准备不能无证明换成原始位置的平稳 Parry 初始混合。不同原始深度的 $[0],[10],\ldots,[1^{k-1}0]$ 各一柱，却在块深度一删掉全部块字母；反向块词 $(1),(0,0)$ 展开为同长的 $10,00$。因此双射或同胚本身不运输预算。

跨表示的继续任务采用 A 卷第 2.17 节与 Context 第 9.8 节的原合同：同一实际起态/历史及共同测试载体，统一的继续测试双射、双向合法性、保持拼接、转移交织、终端观察相同，以及可消去交换幺半群中的可加成本和原始时长均须对应。第 1.3.6 节是这里已交付的具体消费者。集合编码可逆或数字相等不会补出这些操作合同；一般无限字母、约束树、标签法则或不同初态仍各需真实概率、可操作性与长度运输。

**来源与范围 6.7.7。** 本章的六组数学供应分别给出任意 iid 预算交换、有限隐藏及任意历史正性、极点树重标号、有限头比较、指数熵预算和临界停止/状态边界；完整旧 iid 及预算合同的所有者仍是第 5.1–5.8 节。加权分割、概率接口、局部化、Rényi/Perron 和表示运输分别由上文指明的第 4 章及第 1 章承担。普通数学证明、有限整数检查和可计算名字转换是不同证据，不把数值运行当成无限证明。

有限层 Hölder 可直接用所供应钉版 mathlib 的 `Real.inner_le_Lp_mul_Lq_of_nonneg`：在所选有限词集取 $f(w)=\mu[w]$、$g(w)=1$、共轭指数 $s,s/(s-1)$。可数版本 `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` 还需两幂族的可和性；仓内 `countable_weighted_holder_interpolation` 要求非负可和 $f,g$ 和正互补指数，不能由总化 `tsum` 代替这些假设。有限 Rényi 趋一还可直接在 `renyi_divergence_tendsto_kl` 取第二输入恒为一、取负号并限制到右极限；该声明只要求第一输入非负归一化和正支撑上第二输入正，不要求第二输入归一化。`entropy_le_log_card` 用有限非空、非负归一化向量；`collision_entropy_le_shannon_entropy` 只给阶二，不能当一般阶单调性。有限实 KL 声明也不承担定理 6.4.5 的可数停止词 KL；那里已另证可积性并直接给非负性。

概率工具的代入保持同一联合概率律。`iIndepFun_infinitePi` 与坐标推前给 iid 自信息；`strong_law_ae_real` 消费可积、两两独立、同分布，有限正字母使可积而不附收敛速度。CLT 的 `tendstoInDistribution_inv_sqrt_mul_sum_sub` 消费 iid、平方可积及其高斯目标，本章非均匀条件给 $V>0$；连续高斯分布函数才允许所用阈值概率极限。尾零一律 `measure_zero_or_one_of_measurableSet_limsup_atTop` 需要独立尾 $\sigma$ 代数及事件可测性，定理 6.4.2 已逐一验证。Hoeffding 的有界中心变量次高斯参数为 $(R/2)^2$，对 $h-I_i$ 的独立和取偏差 $n^{3/4}/2$，得 $\exp(-\sqrt n/(2R^2))$；均匀的零宽度单独处理。

自然有限概率滤过下，部分和是可积鞅，首次退出为停时。`Submartingale.expected_stoppedValue_mono` 对鞅及负鞅只用于确定有界的 $\sigma\wedge n$；之后以常数 $M+K$ 支配并用 `tendsto_integral_of_dominated_convergence`，才得到原退出的期望等式。几乎必然有限本身不是这个有界停时前提。停止信息的 Tonelli 使用非负项，平均有限只在随后 KL 步骤要求。这些声明源码对应所供应 mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d`（v4.33.0）；这里只核对和使用数学合同，没有进行新的 Lean 构建或组合形式化。

已有两条有限二元 Kraft/前缀自由声明按实际二元、有限、无空词条件使用。第 4.8.2 节已纠正有限唯一可解码“不可检查”的旧注释：有限码的 Sardinas–Patterson 判定是可用边界，旧注释不随本章传播。`markov_chain_law_map_prefix_apply_singleton` 在初态 $p$、常值核 $p$ 下给长度 $n+1$ iid 乘积，空词由归一化处理，保留原 Tau Ceti 与 Apache-2.0 归属；它不证明根律与平稳律相同。有限条件信息充分性仅约束正先验状态，全部有限状态的核分解还需逐点正先验；不是无限拓扑支撑定理。逐点/几乎处处分离中的非空目标条件和非概率 Lebesgue 反例，以及有限边缘相容但有限支撑读数像零测非闭的例子，都只按第 4.8.3 节的原范围使用，不替代本章的有效延拓、逆极限存在或采样结论。

成熟出处沿用第 4.8 节的 Ackerman–Freer–Roy、其所引 Galatolo–Hoyrup–Rojas 与 Hoyrup–Rojas、Pauly–Fouché、Rényi 和 Parry 的准确分工。历史类另与 Beigi–Etesami–Gohari 的 *Deterministic Randomness Extraction from Generalized and Distributed Santha-Vazirani Sources*，[arXiv:1412.6641v1](https://arxiv.org/abs/1412.6641v1)，Definition 1 的有限骰子模型及 Theorem 6 的有限事件 Bellman 递推相接：代入的骰子及混合权已在第 6.1 节写全，它不是无限预算阈值的外部证明。Downey–Melnikov 的 *Computably compact metric spaces*，[作者稿](https://homepages.ecs.vuw.ac.nz/~melnikal/compcomp%28BSL%29.pdf)，Proposition 3.5 是旧有效紧致极值路线的参照；本章直接有限头证书不依赖它。所给来源核对限于供应的版本与范围，未重新核验这些整篇外部论文或完成新颖性检索。

本章给出普通数学证明与可复现有限证书，不主张原创性或新增 Lean 核验。任意临界日程的完整分类、任意实名的精确最优选择、一般最优位复杂度、一般非一致正过程分类及未经证明的表示运输仍未解决。没有引入后续 cofinal、LIL、carry 或 congruence 研究，也没有推出物理空间/时间/频率/熵产生的身份、E7、RH、有限覆盖或逻辑独立性结论。几乎必然有限停止、有限平均长度、有效概率截止、实际公告完成以及无限点的有限正认证各自保持原含义。

## 追加锚（本行以下为增补区）


## 7. 余终分辨率的完整运输：相容线程、精确策略像与等待成本

保留一条无界分辨率子列，可以无损表达原来的相容线程。对一个已经指定的前缀停止策略，把每个停止词展开成下一保留深度的全部后代，也能逐点保留停止事件。但只运输每层允许的码字数量，通常会放宽合法策略集合；恢复指定的原策略需要保留祖先切口，实际延迟等待又有独立的成本。本节在同一组对象上依次证明这些关系，给出精确策略像、有限判定算法、有效恢复条件及全概率律下的可积等待判据。

### 7.1 相容线程的无损抽层

设集合构成逆系统 $X_0\leftarrow X_1\leftarrow\cdots$，复合投影记为 $\pi_{m,n}:X_m\to X_n$，其中 $m\ge n$，并满足 $\pi_{n,n}=\mathrm{id}$ 及 $\pi_{k,n}=\pi_{m,n}\pi_{k,m}$。取严格递增、无界的整数列
$$
S=\{0=n_0<n_1<n_2<\cdots\}.
$$
令 $\mathcal L=\varprojlim_nX_n$、$\mathcal L_S=\varprojlim_jX_{n_j}$，后者的投影继承自原逆系统。

一般极限同构采用 `CategoryTheory.Functor.Initial.limitIso`。具体地，令逆索引范畴 $D$ 的箭头为 $m\to n\iff m\ge n$，保留层索引范畴 $C$ 也取反向整数序，$i:C\to D$ 给 $i(j)=n_j$，图表 $H$ 给 $H(n)=X_n$、$H(m\to n)=\pi_{m,n}$。对每个 $n$，`CostructuredArrow(i,n)` 是不低于 $n$ 的保留层构成的非空尾；任意两层都有共同更高层向它们映射，所以该范畴连通，$i$ 是 initial。在集合范畴中极限存在，既有接口给 $\lim(H\circ i)\cong\lim H$。该接口定义为 `asIso (limit.pre H i)` 的逆，故它的逆方向正是下面的限制映射。

**命题 7.1（既有余终极限同构的坐标适配）。** 限制映射
$$
R:\mathcal L\longrightarrow\mathcal L_S,\qquad R(x)_j=x_{n_j}
\tag{RST.1}
$$
是双射，其逆映射为
$$
R^{-1}(y)_n=\pi_{n_j,n}(y_j),\qquad n_j\ge n.
\tag{RST.2}
$$

证明。无界性保证可选到 $n_j\ge n$。若 $n_k\ge n_j\ge n$，则选中线程的相容性给
$$
\pi_{n_k,n}(y_k)
=\pi_{n_j,n}\bigl(\pi_{n_k,n_j}(y_k)\bigr)
=\pi_{n_j,n}(y_j).
$$
故恢复的坐标不依赖所选高层。对任意原层 $m\ge n$，使用同一个不低于 $m$ 的选中层计算，两坐标满足原投影关系。限制后恢复 $y$，而完整线程限制后再恢复也逐坐标等于原线程。因此两映射互逆。这给出既有同构在相容坐标上的两向公式，不要求层集合有限、投影满射或逆极限非空。$\square$

若各层是拓扑空间、投影连续，逆极限取产品空间的子空间拓扑，则 $R$ 为同胚。限制映射的每个坐标连续；逆映射的第 $n$ 个坐标是某个选中坐标投影后接连续映射 $\pi_{n_j,n}$，也连续。不需要紧性或 Hausdorff 条件。

若各层及投影有统一有效呈示，$j\mapsto n_j$ 全可计算，而且投影统一可计算，则对已经提供的坐标查询名字，$R$ 与 $R^{-1}$ 都可计算。恢复第 $n$ 层时搜索首个 $n_j\ge n$，再调用对应投影；搜索由无界性终止。这里转换的是已给线程的名字，不是从逆系统中构造一个新线程或选择一个点，也没有承诺读取时间、查询长度或计算复杂度界。

### 7.2 完整前缀接口与停止事件的精确运输

固定有限字母表 $A$，$|A|=d\ge2$，路径空间为 $\Omega=A^{\mathbb N}$。$A^*$ 包括空词 $\epsilon$，$A^+=A^*\setminus\{\epsilon\}$。对有限词 $w$，$|w|$ 是其长度，$[w]$ 是以 $w$ 为前缀的柱集；$w\preceq v$ 表示前缀关系。自然过滤 $\mathcal F_n$ 是由完整长度 $n$ 前缀生成的原始过滤，不作依概率律的零集完备化。于是 $\mathcal F_n$ 的原子恰为长度 $n$ 柱集。

停止码 $F\subseteq A^+$ 前缀自由，允许可数无限。记
$$
U_F=\bigcup_{w\in F}[w],\qquad c_n(F)=|F\cap A^n|.
$$
空词被排除，故每个停止深度落在唯一的正层段 $(n_{j-1},n_j]$。定义
$$
m_S(n)=\min\{n_j:n_j\ge n\}\qquad(n\ge1),
\tag{RST.3}
$$
并将每个旧词展开成目标深度上的全部后代：
$$
D_S(F)=\bigcup_{w\in F}wA^{m_S(|w|)-|w|}.
\tag{RST.4}
$$
这里保留全部后缀选择，不能只给每个旧词补一个固定后缀。

**命题 7.2（完整后代展开）。** $D_S(F)$ 前缀自由，每个新词有唯一的旧码字祖先，且
$$
U_{D_S(F)}=U_F.
\tag{RST.5}
$$
在保留深度 $n_j$，其数量精确为
$$
c_{n_j}(D_S(F))
=\sum_{n_{j-1}<n\le n_j}c_n(F)d^{n_j-n};
\tag{RST.6}
$$
其他深度的数量为零。

证明。不同旧码字不可比较，所以任何分别延伸它们的新词也不可比较。同一旧码字产生的新词等长，彼此不同也无前缀关系。因此新码前缀自由，每个新词的旧祖先唯一。对每个 $w\in F$，有有限不交分解
$$
[w]=\bigsqcup_{v\in A^{m_S(|w|)-|w|}}[wv].
\tag{RST.7}
$$
对旧词取并得到式 (RST.5)。目标深度是 $n_j$ 的祖先恰有 $n_{j-1}<|w|\le n_j$；每个长度 $n$ 祖先给出 $d^{n_j-n}$ 个不同新词。唯一祖先排除了重复计数，得到式 (RST.6)。$\square$

因此对 $\Omega$ 上任意同一 Borel 概率律 $\mu$，
$$
\mu(U_{D_S(F)})=\mu(U_F),\qquad
\mu(\Omega\setminus U_{D_S(F)})=\mu(\Omega\setminus U_F).
\tag{RST.8}
$$
这不要求 iid、Markov 性、平稳性、正柱质量、正转移概率或绝对连续性。两边是同一事件；若同时换路径坐标，须推前同一个概率律。

均匀产品律下，每个长度 $n$ 柱质量为 $d^{-n}$；前缀自由码的柱集两两不交，故其质量和不超过一。结合精确计数得到
$$
\begin{aligned}
\sum_{j\ge1}c_{n_j}(D_S(F))d^{-n_j}
&=\sum_{j\ge1}\sum_{n_{j-1}<n\le n_j}c_n(F)d^{-n}\\
&=\sum_{n\ge1}c_n(F)d^{-n}\le1.
\end{aligned}
\tag{RST.9}
$$
所有项非负，重排无需预先假定可和。

保留第 $n_j$ 层，在这里指保留完整长度 $n_j$ 前缀。若只读取第 $n_j$ 个字符，就换了接口。例如 $F=\{0\}$ 延迟到深度二后，事件仍为首位零；路径 $000\cdots$ 与 $100\cdots$ 在所有正偶数位置的字符都相同，停止事件的真值却不同。即使知道全部孤立偶数位，也不能判定该事件。逆系统的相容投影与完整前缀过滤保留了被跳过层的字符，这项条件贯穿后续全部停止运输。

### 7.3 数量预算的运输只给出可行集包络

令 $b_n$ 为有限非负整数，$\mathcal C_b$ 是满足 $c_n(F)\le b_n$ 的所有前缀自由码。定义保留层预算
$$
\beta_j=\sum_{n_{j-1}<n\le n_j}b_nd^{n_j-n}.
\tag{RST.10}
$$
$\beta_j$ 约束的是原始深度 $n_j$，不是深度 $j$。每段有限，所以每个 $\beta_j$ 也是有限整数。令 $\mathcal C_{S,\beta}$ 为只在保留深度停止且满足相应数量界的前缀自由码，则式 (RST.6) 给
$$
D_S(\mathcal C_b)\subseteq\mathcal C_{S,\beta}.
\tag{RST.11}
$$
同时有非负项的重排恒等式
$$
\sum_{j\ge1}\beta_jd^{-n_j}=\sum_{n\ge1}b_nd^{-n}.
\tag{RST.12}
$$
两边允许无穷。预算是上界，不要求所有名额可以同时兑现；某层预算也可大于当层实际可用节点数。

真实展开保留了同一祖先的全部后代必须成束出现的条件。只保留 $\beta_j$，会允许名额在该深度重新分配，所以式 (RST.11) 不保证为等号。对同一概率律定义
$$
M_b(\mu)=\sup_{F\in\mathcal C_b}\mu(U_F),\qquad
M_{S,\beta}(\mu)=\sup_{G\in\mathcal C_{S,\beta}}\mu(U_G).
$$
逐码事件相等与像包含仅给出
$$
M_b(\mu)\le M_{S,\beta}(\mu).
\tag{RST.13}
$$
若右边只对真实像 $D_S(\mathcal C_b)$ 取上确界，才精确等于 $M_b(\mu)$。

### 7.4 均匀最优值及两个有限反例

**命题 7.3（均匀饱和定理的保留容量适配）。** 对均匀 $d$ 元产品律 $\lambda$，令 $K=\sum_{n\ge1}b_nd^{-n}$，允许 $K=\infty$。则
$$
M_b(\lambda)=\min\{1,K\}=M_{S,\beta}(\lambda).
\tag{RST.14}
$$
这些最优值可由允许可数无限的合法码取得。

证明。推论 6.1.3已经证明任意非负整数预算下的均匀饱和公式及可数码取到性。其原预算取 $b$；保留策略则在原始深度上取
$$
\widetilde b_n=\begin{cases}\beta_j,&n=n_j,\\0,&n\notin S.\end{cases}
$$
于是 $\mathcal C_{\widetilde b}=\mathcal C_{S,\beta}$，式 (RST.12) 使两者在该定理中的总预算质量均为 $K$，得到式 (RST.14)。为明确这个适配的整数容量和取到性，沿用该节的构造：Kraft 不等式与逐层预算给上界；按深度递增构造码。若此前累计停止质量为 $p_{n-1}$，尚未被旧码覆盖的长度 $n$ 节点有整数 $d^n(1-p_{n-1})$ 个。在固定字序下取其中与 $b_n$ 两者较小的数量。若某层填满剩余树，累计质量已经为一；若一直未填满，则每层都取满 $b_n$，最终质量为 $K\le1$。当 $K>1$ 或 $K=\infty$ 时，后一情形不可能；当 $K=1$ 时，可以在无限极限中才达到一。若 $K=0$，空码取到零；$K=1$ 的无穷取到包括上述未在有限层填满的情形。预算大于可用节点数时只取剩余节点，因而无需假定 $b_n\le d^n$。对 $\widetilde b$，非保留层取零个节点，保留层正按 $\beta_j$ 取节点；这就是同一构造的保留层适配。$\square$

相同的最优概率不说明策略族相同，更不说明旧停止长度相同。非均匀源甚至可以严格改变最优值。

**反例 7.1（包络提高非均匀容量）。** 取二元 iid 律 $p(0)=9/10$、$p(1)=1/10$，仅有 $b_1=1$ 非零。原最优码 $\{0\}$ 给
$$
M_b(p)=\frac9{10}.
\tag{RST.15}
$$
保留深度 $n_j=3j$，则仅 $\beta_1=4$ 非零。真实展开为 $\{000,001,010,011\}$，质量仍为 $9/10$。长度三词的质量按含一数量排列如下：

| 含一数量 | 词数 | 单词质量 |
|---:|---:|---:|
| 0 | 1 | $729/1000$ |
| 1 | 3 | $81/1000$ |
| 2 | 3 | $9/1000$ |
| 3 | 1 | $1/1000$ |

包络允许选择四个最重词 $G=\{000,001,010,100\}$，所以精确有
$$
M_{S,\beta}(p)=\frac{729+3\cdot81}{1000}
=\frac{243}{250}>\frac9{10},\qquad
\frac{243}{250}-\frac9{10}=\frac9{125}.
\tag{RST.16}
$$
任何长度一单词的完整三层后代束都具有相同首位，$G$ 不满足这一条件，故不是真实像。两预算的 Kraft 总量却同为
$$
1\cdot2^{-1}=4\cdot2^{-3}=\frac12.
\tag{RST.17}
$$
改变最优值的是策略约束放宽，并非同一事件的概率发生变化。

**反例 7.2（重新套用原数值规则降低容量）。** 在均匀二元源中，只许深度一取一个词时最优值为 $1/2$；改为只许深度二取一个词时为 $1/4$。旧词准确展开需要两个深度二后代，质量才仍为 $1/2$。无损抽去观察层与重新指定停止预算是不同操作。

### 7.5 精确策略像是受深度容量约束的树切口

给定仅在 $S$ 的正深度停止的前缀自由码 $G$。对第 $j$ 段令 $l=n_{j-1}$、$r=n_j$、$G_j=G\cap A^r$，定义可用祖先集合
$$
\mathcal B_j=\{w\in A^*:l<|w|\le r,\quad
wA^{r-|w|}\subseteq G_j\}.
\tag{RST.18}
$$
每个可用祖先必须具有完整后代束。

**命题 7.4（精确像判据）。** 存在 $F\in\mathcal C_b$ 使 $G=D_S(F)$，当且仅当每段都有 $x_w\in\{0,1\}$，$w\in\mathcal B_j$，满足
$$
\sum_{\substack{w\in\mathcal B_j\\w\preceq g}}x_w=1
\quad(g\in G_j),\qquad
\sum_{\substack{w\in\mathcal B_j\\|w|=n}}x_w\le b_n
\quad(l<n\le r).
\tag{RST.19}
$$

证明。若 $G=D_S(F)$，本段的原码字均属于 $\mathcal B_j$。取它们的指标作为 $x_w$。每个展开叶有唯一旧祖先，所以叶子方程为一；原码预算给第二组不等式。

反向取 $F_j=\{w\in\mathcal B_j:x_w=1\}$。若两个不同的所选祖先可比较，较深者至少有一个长度 $r$ 后代，完整性使该后代属于 $G_j$，且位于两个所选祖先下方，违反叶子方程。故 $F_j$ 前缀自由。叶子方程保证覆盖 $G_j$ 的每个叶子；可用祖先定义排除覆盖 $G_j$ 以外的叶子，因此
$$
\bigcup_{w\in F_j}wA^{r-|w|}=G_j.
$$
跨段也不产生前缀冲突。设早段目标深度为 $r$，晚段所选词为 $v$。晚段词的长度大于其前段边界，故大于 $r$。若早段所选祖先 $w$ 是 $v$ 的前缀，则 $v|_r$ 位于 $w$ 的完整后代束中，属于 $G$。晚段 $v$ 的任一展开叶也属于 $G$ 且延伸 $v|_r$，违反 $G$ 前缀自由。反方向的前缀关系由长度排除。因此 $F=\bigcup_jF_j$ 为前缀自由码，每个深度的预算由其唯一所属段保证，且 $D_S(F)=G$。

每段问题有限，可在固定字序及固定子集顺序下选择第一份可行切口，以此定义全局 $F$，无需另设任意无限选择数据。若 $G_j=\varnothing$，则 $\mathcal B_j=\varnothing$，本段唯一切口为空；深度 $r$ 的叶子允许入选，深度 $l$ 的节点不允许入选。$\square$

这个判据也可理解为完整兄弟叶的收缩：只允许收缩到严格深于 $l$ 的祖先，并须使最终切口满足原逐深度预算。可行切口不能自动选成最短祖先。

**反例 7.3（最短切口不保证合法）。** 取 $l=0$、$r=3$、$G_j=\{000,001,010,011\}$，仅 $b_2=2$ 非零。切口 $\{00,01\}$ 合法；把它再合为 $\{0\}$ 则违反 $b_1=0$。表示长度更短与原预算合法是两个判据。

### 7.6 有限段的精确动态规划及可计算合法原像

对 $|v|\le r$，记 $E_v=\{g\in G_j:v\preceq g\}$。用变量 $z_{l+1},\ldots,z_r$ 定义生成多项式 $P_v$，指数记录切口中每个深度的祖先数，系数记录具有该计数的不同切口数。

若 $E_v=\varnothing$，置 $P_v=1$，表示唯一空切口。若 $|v|=r$ 且 $v\in G_j$，置 $P_v=z_r$。其余非空内部节点满足
$$
P_v=\prod_{a\in A}P_{va}
+\begin{cases}
z_{|v|},&l<|v|<r\text{ 且 }E_v=vA^{r-|v|},\\
0,&\text{其他情况}.
\end{cases}
\tag{RST.20}
$$

**命题 7.5（精确计数与容量截断）。** 根多项式 $P_\epsilon$ 中单项式 $\prod_{n=l+1}^rz_n^{c_n}$ 的系数，是该段完整切口中具有深度计数 $(c_n)$ 的切口数量。存在满足原预算的切口，当且仅当其中有正系数单项式满足 $c_n\le b_n$。

证明。对节点高度归纳。空子树只有空切口，所以是常数一而非零；非空目标叶只能选自身。内部节点若不选自身，各子树中切口的选择彼此独立，其并为唯一的整体切口；反向整体切口在各子树上的限制也唯一，故用乘积精确计数。选自身仅在节点深于 $l$ 且后代完整时合法，形成额外单项式，并与所有下分选择互斥。不同切口即使给出同一计数向量，仍由系数累加。根及深度 $l$ 的节点不可选，所以没有越过本段边界的收缩。归纳得到结论。$\square$

运算时可立即删除任一指数超过预算的单项式。相乘只会增加非负指数，相加的系数也非负，没有抵消；被删除项不可能再对容量内项贡献。因此逐步截断不仅保留可行性，也保留所有容量内单项式的精确系数。每张截断表的指数向量数量至多
$$
\prod_{n=l+1}^r(b_n+1).
\tag{RST.21}
$$
若直接访问从根到深度 $r$ 的整棵 $d$ 元树，节点数为 $\sum_{i=0}^r d^i$，确定 $G_j$ 需 $d^r$ 次叶成员查询；计数系数也须用足够位数的整数保存。式 (RST.21) 不控制这些系数位数、树节点总量、多项式乘法代价或压缩输入长度。算法有限有效，不据此声称二进制输入下的多项式时间复杂度。

假设有效给定字母表、计算 $j\mapsto n_j$ 与 $n\mapsto b_n$ 的总程序、$G$ 的总成员决定器，并承诺 $S$ 严格递增无界、$G$ 全局前缀自由且仅含正保留层词、每段都可行。对每段运行此动态规划，按固定顺序选取可行根项，并以固定顺序回溯得到切口 $F_j$。这给一份可计算合法原码：对输入非空词 $w$，先求唯一的
$$
n_{j-1}<|w|\le n_j,
\tag{RST.22}
$$
再用决定器查完长度 $n_j$ 的全部有限词，形成 $G_j$，读取本段有限预算并求出所选切口，判断 $w\in F_j$。空词直接拒绝。每个输入只需要有限一段，承诺使回溯能成功；无需先完成其他无穷多段。命题 7.4 保证逐段结果共同构成全局合法码。

若只给可枚举的 $G$，尚未出现的有限叶子不能被当成不存在，上述决定算法不再由同一输入合同保证。这不证明每种特殊可枚举输入都不可能选取原像，也不把“指定旧码不可恢复”误解成“某个合法原像不可选择”。


例如反例 7.3 的目标叶给出
$$
P_\epsilon=z_1+(z_2+z_3^2)^2
=z_1+z_2^2+2z_2z_3^2+z_3^4.
$$
系数二对应分别在左、右两个深度二子树中选择下分的两份切口。容量 $(b_1,b_2,b_3)=(0,2,0)$ 截断后只剩 $z_2^2$，其唯一切口为 $\{00,01\}$。

### 7.7 祖先标记、原适应性与指定策略的恢复

精确像判据可以选择一个合法原像；要恢复此前实际选定的那一个原像，还须携带相应切口。对仅在保留深度停止的前缀自由码 $G$，给祖先映射 $a:G\to A^+$，要求 $a(g)\preceq g$、$|g|=m_S(|a(g)|)$，并令 $F=a(G)$ 满足
$$
\begin{gathered}
F\text{ 前缀自由},\qquad |F\cap A^n|\le b_n,\\
\{g\in G:a(g)=w\}=wA^{m_S(|w|)-|w|}\qquad(w\in F).
\end{gathered}
\tag{RST.23}
$$

**命题 7.6（有标记策略等价）。** $F\in\mathcal C_b$ 与满足式 (RST.23) 的 $(G,a)$ 一一对应。正向为完整展开及唯一旧祖先标记，反向为 $F=a(G)$。

证明。命题 7.2 给出正向合法性及祖先唯一性。反向逐祖先取式 (RST.23) 的完整标记纤维之并，得到 $G=D_S(F)$。$F$ 前缀自由，故每个 $g$ 只有一个 $F$ 祖先，重建的祖先映射就是原 $a$。正反组合分别恢复 $F$ 和整个 $(G,a)$。空码对应空码及唯一空映射。$\square$

祖先无需重复存成完整词：给定 $g$，保留深度 $\ell(g)=|a(g)|$ 就足以恢复 $a(g)=g|_{\ell(g)}$。这里证明的是深度标记充分，没有证明其在比特数、压缩长度或任何编码模型中最小。

将标记延拓为路径函数
$$
L(x)=\begin{cases}
\ell(g),&x\in[g],\ g\in G,\\
\infty,&x\notin U_G.
\end{cases}
\tag{RST.24}
$$
前缀自由性使定义唯一。对任意停止码 $H$，记 $\tau_H$ 为命中唯一 $H$ 前缀的深度，未命中时取 $\infty$。式 (RST.23) 等价于以下路径条件：$L$ 是原始完整前缀过滤的停止时间；每个 $\{L=n\}$ 是至多 $b_n$ 个长度 $n$ 柱集的并；对 $g\in G_j$，在 $[g]$ 上恒有 $n_{j-1}<L\le n_j$；且 $L=\infty$ 恰在 $\Omega\setminus U_G$。

证明。合法完整祖先束对应原停止码，给出的 $L$ 正是其停止深度，以上条件立即成立。反向，原停止适应性给 $\{L=n\}=\{L\le n\}\setminus\{L\le n-1\}\in\mathcal F_n$。原始过滤的有限原子恰为全部长度 $n$ 柱集，故对每个 $n$ 选出构成 $\{L=n\}$ 的长度 $n$ 柱集，令它们的词组成 $F\cap A^n$。这些事件两两不交；若不同所选词可比较，其柱集会相交，矛盾。因此 $F$ 前缀自由，且计数满足预算。

若 $w\in F$、$|w|=n$，令 $r=m_S(n)$。任意延伸 $w$ 的路径都满足 $L=n<\infty$，所以落在某个 $G$ 柱中；该柱所属段的范围条件迫使其长度恰为 $r$。因此 $w$ 的每个长度 $r$ 后代均在 $G$，且标记均为 $n$。反向，每个 $g\in G_j$ 的任一路径具有同一有限标记 $n=\ell(g)$，相应长度 $n$ 前缀必在所构造的 $F$ 中。于是标记纤维恰是完整后代束，并且逐路径有
$$
m_S(L)=\tau_G,
\tag{RST.25}
$$
其中 $m_S(\infty)=\infty$，$\tau_G$ 是 $G$ 的停止深度。$\square$

例如取偶数保留层及 $G=\{00,01\}$，在 $00$ 上给数字一、在 $01$ 上给数字二，域外取无穷。两数字都落在合法层段 $(0,2]$，且都能在深度二读到，但 $\{L=1\}=[00]\notin\mathcal F_1$：长度一原子 $[0]$ 的一部分被赋一，另一部分被赋二。因此这些晚到数字不是原停止深度，深度一的完整祖先束也被割裂。

原适应性实际承担了完整束条件。只在延迟读取时得到某个数字，若没有上述原始过滤下的停止时间条件，不能将其当成合法旧策略。采用原始过滤也使这里的结论是全路径相等，不是忽略零概率柱后的几乎处处替代。

### 7.8 恢复旧记录成本不消除真实等待

给定任意非负原终止词成本 $k:A^+\to[0,\infty]$。在延迟词 $g$ 上计 $k(g|_{\ell(g)})$，则停止路径上的旧记录成本逐点恢复；未停止路径两边采用同一个另行指定的非负可测成本函数 $h:\Omega\setminus U_F\to[0,\infty]$。对任何共同概率律，
$$
\sum_{g\in G}\mu([g])k(g|_{\ell(g)})
=\sum_{w\in F}\mu([w])k(w).
\tag{RST.26}
$$
这里非负扩实乘积按积分惯例理解，特别约定 $0\cdot\infty=0$，即零质量柱对非负成本积分的贡献为零。加上两边相同的 $\int_{\Omega\setminus U_F}h\,d\mu$，便得到完整路径成本的期望恒等式。

证明。对每个 $w\in F$，完整标记纤维将 $[w]$ 有限不交地分成延迟柱，各柱上都计同一成本 $k(w)$。先在这个有限束上积分，再对所有原词取非负和，得到式 (RST.26)。不需要 iid、正柱质量或预先可积性。更直接地，两侧恢复的路径成本函数相同，因而其分布及非负期望相同。$\square$

若成本还依赖原停止词未确定的其他状态，须另行保留该状态；上式没有自动涵盖这类信息。实际读取或等待成本仍为 $|g|$，不是标记深度 $\ell(g)$。

**反例 7.4（遗忘标记丢失旧策略及成本）。** 保留偶数深度。$F_1=\{0\}$ 与 $F_2=\{00,01\}$ 都展开成 $G=\{00,01\}$。若预算同时允许 $b_1\ge1$、$b_2\ge2$，两者都合法。在同一公平源下，未停止成本取零，旧有限停止字长成本分别为
$$
\sum_{w\in F_1}|w|\lambda([w])=\frac12,\qquad
\sum_{w\in F_2}|w|\lambda([w])=1.
\tag{RST.27}
$$
这里计的是有限停止字长、未停止取零的成本；若把未停止时间定义为无穷，则两个 $\mathbb E\tau_{F_i}$ 都为无穷，不能用它们代替式 (RST.27)。条件于停止事件 $[0]$，两份旧时间分别恒为一和二。故没有仅依赖无标记 $G$ 的规则能恢复每一个被遗忘原像的旧成本；这不排除第 7.6 节算法选择某个合法原像。

### 7.9 延迟停止、过滤与精确尾和

令 $\tau_F(x)$ 为路径命中 $F$ 的深度，未命中时为 $\infty$。前缀自由性保证有限命中词唯一。逐路径有
$$
\tau_{D_S(F)}=m_S(\tau_F).
\tag{RST.28}
$$
证明。命中旧词 $w$ 的路径在深度 $m_S(|w|)$ 命中其完整后代束。若更早命中其他新束，将给出另一个 $F$ 前缀，与前缀自由性矛盾。未命中旧码的路径也不在任一新柱中。$\square$

令 $\mathcal G_j=\mathcal F_{n_j}$，并定义
$$
J_F=\min\{j\ge1:\tau_F\le n_j\},
\qquad J_F=\infty\text{ 若该集合为空}.
\tag{RST.29}
$$
因为 $\{J_F\le j\}=\{\tau_F\le n_j\}\in\mathcal G_j$，$J_F$ 是选层过滤的停止时间。若在原始整数时钟上保持最近完整记录，令 $s(n)=\max(S\cap[0,n])$、$\mathcal H_n=\mathcal F_{s(n)}$，则
$$
\{m_S(\tau_F)\le n\}=\{\tau_F\le s(n)\}\in\mathcal H_n.
$$
所以延迟时间同时适应这个保持过滤和原过滤；没有在未观察的时刻读取将来的字符。按原始步数计费的延迟为 $n_{J_F}$，无穷索引对应无穷延迟。保留深度上的尾分布满足
$$
\Pr\{\tau_{D_S(F)}>n_j\}=\Pr\{\tau_F>n_j\},
\tag{RST.30}
$$
因为 $m_S(t)>n_j$ 等价于 $t>n_j$，包括 $t=\infty$。

逐路径的非负指示分解为
$$
\begin{aligned}
\tau_F&=\sum_{n\ge0}\mathbf1_{\{\tau_F>n\}},\\
m_S(\tau_F)&=\sum_{j\ge1}(n_j-n_{j-1})\mathbf1_{\{\tau_F>n_{j-1}\}},\\
J_F&=\sum_{j\ge1}\mathbf1_{\{\tau_F>n_{j-1}\}}.
\end{aligned}
$$
有限停止时分别是计数与望远镜和；无限停止时无界层列使三式均为无穷。由 Tonelli 得
$$
\begin{aligned}
\mathbb E\tau_F&=\sum_{n\ge0}\Pr(\tau_F>n),\\
\mathbb E\tau_{D_S(F)}
&=\sum_{j\ge1}(n_j-n_{j-1})\Pr(\tau_F>n_{j-1}),\\
\mathbb E J_F&=\sum_{j\ge1}\Pr(\tau_F>n_{j-1}).
\end{aligned}
\tag{RST.31}
$$
这些都是非负扩实恒等式，没有有限均值前提。阶段数与原始等待长度是两个成本单位。

若每段间距 $n_j-n_{j-1}\le g$，其中有限整数 $g\ge1$，则
$$
\tau_F\le\tau_{D_S(F)}\le\tau_F+g-1.
\tag{RST.32}
$$
若有 $C\ge1$ 使 $n_j\le C(n_{j-1}+1)$，则
$$
\tau_F\le\tau_{D_S(F)}\le C\tau_F.
\tag{RST.33}
$$
证明。在有限命中所在段内，$n_{j-1}+1\le\tau_F\le n_j$。于是 $n_j-\tau_F\le n_j-n_{j-1}-1\le g-1$，且 $n_j\le C(n_{j-1}+1)\le C\tau_F$。下界来自向上取层；无穷路径以扩实约定处理。积分后得到对应期望界。恒等层列 $n_j=j$ 给逐路径完全相等；对任意层列，若原码仅在保留层停止，也有 $m_S(\tau_F)=\tau_F$。$\square$

### 7.10 对全部概率律保留可积等待的精确条件

定义
$$
C_S=\sup_{j\ge1}\frac{n_j}{n_{j-1}+1}
=\sup_{n\ge1}\frac{m_S(n)}n.
\tag{RST.34}
$$
等号成立，因为在每段内 $m_S(n)=n_j$，比值随正整数 $n$ 递减，在 $n=n_{j-1}+1$ 取得本段最大值。

**命题 7.7（全律可积性判据）。** 以下三个条件等价：$C_S<\infty$；$m_S(n)=O(n)$；对每个概率空间及其上每个正整数值随机变量 $T$，都有
$$
\mathbb ET<\infty\quad\Longrightarrow\quad
\mathbb E m_S(T)<\infty.
\tag{RST.35}
$$

证明。有限 $C_S$ 给全局线性上界，也给式 (RST.35)。反过来，一个最终成立的 $O(n)$ 上界可以吸收有限多个初始比值，所以与 $C_S<\infty$ 等价。

若 $C_S=\infty$，任意有限前缀上的比值仍有限，因此可递归选出严格递增 $t_k\ge2$，满足 $m_S(t_k)/t_k\ge k^3$。令
$$
\Pr(T=t_k)=\frac1{4k^2t_k},\qquad
\Pr(T=1)=1-\sum_{k\ge1}\frac1{4k^2t_k}.
\tag{RST.36}
$$
这是合法概率分布：对 $k\ge2$ 有 $k^{-2}\le1/(k(k-1))=1/(k-1)-1/k$，故望远镜和给 $\sum_{k\ge1}k^{-2}\le2$，故所分配总质量至多 $\frac18\sum k^{-2}\le1/4$。由此
$$
\mathbb ET\le1+\frac14\sum_{k\ge1}\frac1{k^2}<\infty,\qquad
\mathbb E m_S(T)\ge\sum_{k\ge1}\frac{k}{4}=\infty.
\tag{RST.37}
$$
式 (RST.35) 因而失败，完成必要性。$\square$

该反例也可在同一前缀停止模型中实现。选两个字母 $0,1$，固定首次零码 $F=\{1^{n-1}0:n\ge1\}$；把式 (RST.36) 的质量放在路径 $1^{t_k-1}00\cdots$ 上，其余质量放在 $000\cdots$。这是同一条路径空间上的原子 Borel 律，首次零时间恰具有 $T$ 的分布。这个码在每个正深度恰有一个词，故例如 $b_n\ge1$ 对全部 $n$ 成立的策略类容纳该见证。因此允许这个策略及全部共同 Borel 律时，必要性已经在前缀模型内成立。

这项必要性的量词是全部正整数随机变量，或允许容纳上述首次零码的前缀策略及全部共同律；它不是某个固定 iid 律的分类，也没有证明对任意预先给定的苛刻预算都必要。例如，只准在一个有限深度 $N$ 停止时，有限 $\mathbb E\tau_F$ 迫使几乎处处停在 $N$，延迟期望就是有限数 $m_S(N)$，对任意余终层列均成立。全零预算只容纳空码，$\tau_F=\infty$，有限均值前提从不成立，故该蕴含真值是空泛的。这两类预算均不提供上述必要性见证。充分性 $m_S(T)\le C_ST$ 则适用于任何预算允许的策略。

对固定源与固定策略，可积性由式 (RST.31) 的加权尾和是否有限精确决定。“层间距无界”本身不强迫每个策略延迟均值无限；若策略本就只在保留层停止，则 $m_S(\tau_F)=\tau_F$。

### 7.11 可计算抽层将有限均值变成无限均值

**反例 7.5（同事件、可判定码、不同等待可积性）。** 在公平二元源下，取首次零码 $F=\{1^{n-1}0:n\ge1\}$。它满足
$$
\Pr(\tau_F=n)=2^{-n}\ (n\ge1),\qquad
\Pr(\tau_F>n)=2^{-n}\ (n\ge0),\qquad
\mathbb E\tau_F=2.
\tag{RST.38}
$$
停止在 $n$ 要求前 $n-1$ 位都是一、第 $n$ 位是零，所以概率为 $2^{-n}$；超过 $n$ 只要求前 $n$ 位都是一，所以尾概率也为 $2^{-n}$。式 (RST.31) 给 $\mathbb E\tau_F=\sum_{n\ge0}2^{-n}=2$。停止事件恰为除全一串以外的全部路径，而全一串质量为 $\lim_n2^{-n}=0$，因而该事件满测。令
$$
n_0=0,\qquad n_j=2^{n_{j-1}},
\tag{RST.39}
$$
每一步整数幂运算终止，所以层列可计算。对 $n=0$ 有 $2^n>n$；对 $n\ge1$，$2^1>1$，且 $2^{n+1}=2\cdot2^n>2n\ge n+1$，归纳给 $2^n>n$。因而各步严格增加，且整数列满足 $n_j\ge j$，从而无界，前几层为 $0,1,2,4,16,65536,\ldots$。按停止块求和，延迟时间 $\tau'=m_S(\tau_F)$ 满足
$$
\begin{aligned}
\mathbb E\tau'
&=\sum_{j\ge1}n_j\Pr(n_{j-1}<\tau_F\le n_j)\\
&=\sum_{j\ge1}n_j(2^{-n_{j-1}}-2^{-n_j})\\
&=\sum_{j\ge1}(1-n_j2^{-n_j})=\infty.
\end{aligned}
\tag{RST.40}
$$
对所有整数 $n\ge1$，$2^{n-1}\ge n$ 的初值 $n=1$ 是等号；若它在 $n$ 成立，则 $2^n\ge2n\ge n+1$，所以归纳成立。因此 $n2^{-n}\le1/2$，式 (RST.40) 每项至少为 $1/2$，前 $m$ 项至少为 $m/2$。这是对无限级数的下界证明。

该层新码字数量及质量还可由精确计数直接得到：
$$
\sum_{n=n_{j-1}+1}^{n_j}2^{n_j-n}
=2^{n_j-n_{j-1}}-1,\qquad
\lambda(\tau'=n_j)=2^{-n_{j-1}}-2^{-n_j}.
\tag{RST.41}
$$
层质量求和望远镜消去为一。因此新旧事件逐点相同，新旧 Kraft 和也都为一。前四个停止块的等待贡献依次为 $1/2,1/2,3/4,4095/4096$，累计 $11263/4096$；第五项为 $1-2^{-65520}$。令 $a_j=2^{-n_j}$，尾和截断与停止块截断分别为
$$
Q_m=\sum_{j=1}^m(n_j-n_{j-1})a_{j-1},\qquad
B_m=\sum_{j=1}^mn_j(a_{j-1}-a_j).
$$
相减得 $Q_m-B_m=\sum_{j=1}^m(n_ja_j-n_{j-1}a_{j-1})=n_ma_m$，因为 $n_0=0$。故精确有 $Q_m-B_m=n_m2^{-n_m}>0$，有限截断不能混作同一数。例如第四段尾和为 $11/4$，比上述累计多 $1/4096$。

另一方面，严格递增整数层列满足 $n_j\ge j$，所以 $J_F\le\tau_F$，从而 $\mathbb EJ_F\le2$。无限的是原始等待步数的均值，不是观察阶段数的均值。原码可判定，层列可计算，第 7.12 节的算法还保证延迟码可判定，所以发散不依赖不可计算的成员判定。

### 7.12 可枚举、可判定及在线执行的不同接口

以下有效性结论都要求有效给定字母表、保留层列，以及所用的统一程序；不是仅对每个单独对象断言存在某个未提供算法。

若 $F$ 可枚举，则 $D_S(F)$ 可枚举。枚举到 $w$ 后，计算 $m_S(|w|)$ 并输出其全部有限后代。每包再大也是有限，故依次处理不会被某个无限输出包永久阻塞；不承诺实用的运行时间或输出规模。

若 $F$ 可判定，则 $G=D_S(F)$ 可判定。输入空词直接拒绝；对非空 $g$，搜索首个 $n_j\ge|g|$，若不相等便拒绝。相等时有
$$
g\in G\quad\Longleftrightarrow\quad
\exists n\in\{n_{j-1}+1,\ldots,n_j\}:g|_n\in F.
\tag{RST.42}
$$
右侧只有有限次成员判定。该段外祖先不能展开到本层，段内命中祖先由前缀自由性唯一，因此祖先标签也可计算。

反向给定合法标记 $(G,a)$。标签只需由一个统一部分可计算程序给出，并保证在每个 $g\in G$ 上终止；不要求在域外终止。若 $G$ 可枚举，枚举成员并交错运行其标签程序，输出所有祖先。每个祖先完整纤维非空，所以恰枚举出 $F$。

若 $G$ 可判定，固定一个字母 $a_0$。对非空候选 $w$ 构造 $g=wa_0^{m_S(|w|)-|w|}$，则
$$
w\in F\quad\Longleftrightarrow\quad g\in G\text{ 且 }a(g)=w.
\tag{RST.43}
$$
先运行 $G$ 决定器；若否便拒绝，若是才运行标签程序，此时保证终止。完整束保证正向，反向来自标签的原像定义。即使同一测试词有另一个旧祖先，标签比较也会正确排除候选 $w$。由此 $F$ 可判定。

无标记新码不能恢复指定的被遗忘旧码，见反例 7.4；在额外的可判定输入和可行性承诺下，第 7.6 节仍能选择某个合法原像，这两项结论相容。

数学停止时间与在线执行时间也不同。仅有可枚举呈示时，一个浅码字可在任意晚的枚举阶段才被公布，不能据此声称读取到该深度时就有会终止的在线判定。前缀深度、枚举阶段、判定运行时间、观察次数和实际等待成本须分别核算。

### 7.13 嵌套抽层的组合律

若 $T=\{0=t_0<t_1<\cdots\}$ 是 $S$ 的无界子列，则
$$
m_T(m_S(n))=m_T(n).
\tag{RST.44}
$$
证明。首个不小于 $n$ 的 $T$ 层自身属于 $S$，因而不小于 $m_S(n)$；反向，不小于 $m_S(n)$ 的 $T$ 层也不小于 $n$。二者的首个合格层相同。$\square$

完整展开因而满足
$$
D_T(D_S(F))=D_T(F).
\tag{RST.45}
$$
对每个旧祖先，第一轮等长后代分割了第二轮全部后缀选择；先展开到 $S$ 再展开到 $T$ 与直接展开到 $T$ 给出同一组词，无重复也无遗漏。有标记时，若 $a_S:D_S(F)\to F$、$a_{T\mid S}:D_T(D_S(F))\to D_S(F)$ 是两级唯一祖先映射，则合成标记为 $a_S\circ a_{T\mid S}$。对任意 $w\in F$，所有中间后代恰填满深度 $m_S(|w|)$ 的束；每个中间后代又填满终层的后缀。由式 (RST.44)，这些互不重叠的小束之并正为 $wA^{m_T(|w|)-|w|}$，故复合标记的整个纤维是原祖先的完整终层束。它等于直接展开的唯一祖先标记，也保持原深度预算与按原祖先定义的成本。

预算包络也满足
$$
\begin{aligned}
\sum_{t_{i-1}<n_j\le t_i}\beta_jd^{t_i-n_j}
&=\sum_{t_{i-1}<n_j\le t_i}
  \sum_{n_{j-1}<n\le n_j}b_nd^{t_i-n}\\
&=\sum_{t_{i-1}<n\le t_i}b_nd^{t_i-n}.
\end{aligned}
\tag{RST.46}
$$
因为相邻原段恰分割 $(t_{i-1},t_i]$，且两次展开权重相乘为 $d^{t_i-n}$。不要求预算和有限，也不要求预算全部可用。这是数值包络算子的组合；若中间已经遗忘完整束而放宽策略，后续数值组合不会自动删除额外策略。

嵌套条件不可略去。例如 $S=\{0,2,4,6,\ldots\}$、$T=\{0,1,3,5,\ldots\}$ 时，$m_T(m_S(1))=3$，而 $m_T(1)=1$。

### 7.14 变长块坐标与稀疏预算

将原路径切成长度 $n_j-n_{j-1}$ 的连续块，得到无损坐标
$$
A^{\mathbb N}\cong\prod_{j\ge1}A^{n_j-n_{j-1}}.
\tag{RST.47}
$$
具体地，分块映射取第 $j$ 块为字符位置 $n_{j-1}+1,\ldots,n_j$。反向将依次给出的有限块连接；任一位置属于唯一有限块，无界性保证没有未覆盖的位置。分块后连接恢复每个原字符，连接后再分块恢复每个原块，所以两映射互逆。每个有限块由一个有限前缀决定，每个原始有限前缀由有限多个块决定，故产品离散拓扑下两向都连续。有效层列下搜索该有限块并拼接，也给已经提供的坐标名字的可计算转换。

均匀源的第 $j$ 块有 $d^{n_j-n_{j-1}}$ 种选择，前 $j$ 块的一个完整柱质量为 $d^{-n_j}$，一般不是 $d^{-j}$。非均匀 iid 源须保留各块真实产品权重；任意历史律须保留真实共同块联合律。

在密集深度使用预算 $b_n$，再在稀疏深度直接重采样为 $b_{n_j}$，与运输成式 (RST.10) 的 $\beta_j$ 是不同任务。稀疏停止机会减少且未支付旧码全部后代预算，可以降低截获容量；支付 $\beta_j$ 后若又遗忘完整束约束，也可以增加非均匀源上的容量。两者均不反驳线程的无损抽层。

跨深度停止事件的质量由式 (RST.8) 控制，放宽可行集后的最优值由式 (RST.13) 比较，旧记录成本由式 (RST.26) 运输，原始等待则由式 (RST.28)–(RST.40) 计算。完整对象、观察接口、合法策略、共同律和费用必须一并声明，才能确定某次换表示究竟保留什么。

### 7.15 既有接口、成熟来源与适用边界

相容线程与原状态的区别沿用第 2.1.4、2.2.4 节。`D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean` 的 `RefinementSystem` 在当前模型取 $X=\Omega$、第 $n$ 层 `Coordinate` 为 $A^n$、`readout` 为完整前缀、相邻 `restrict` 为截断。所有前缀相等蕴含每个字符相等，故分离路径；相容有限前缀按位置连接为一条路径，且每个前缀读数正确，故满足 `ThreadComplete`。这两项正是 `stateThread_bijective_iff_complete_and_separates` 的条件。`stateEquivInverseLimit` 是非计算性定义；一般逆系统中第 7.1 节只比较两种线程空间，不由此许诺存在实现它们的另一个原状态空间。第 2.2.5 节的实际 LCM 塔已有具体有效余终搜索背景，搜索终止仍须来自其明示的层列条件。

一般余终极限同构的所属接口为钉版 `Mathlib/CategoryTheory/Limits/Final.lean` 中 `CategoryTheory.Functor.Initial.limitIso`；第 7.1 节给出 $D,C,i,H$ 的具体代入、initial 性及逆方向与限制映射的对应。该库声明使用一般极限和非计算性选择；这里的向上搜索名字转换由显式算法另行承担，不能由一个抽象同构自动取得复杂度界。

`D5/S0/Computability/Coding/PrefixFreeCode.lean` 中取字母参数 $\alpha=A$、词集参数为 $F$ 或 $G$，使用 `IsPrefixFree`。其 `isPrefixFree_first_codeword` 在前缀自由、两首词均属码集及两份拼接词相等的条件下，给出首词与余后缀各相等；停止码另排除空词，避免空词反复拼接的歧义。其 `kraft_inequality_of_isPrefixFree` 实际输入是有限二元 `Finset (List (Fin 2))`，并有前缀自由及无空词前提。第 7.2 节的任意 $d$、可数码及任意共同律结论由不交柱集和非负求和证明承担。有限唯一可译码的判定边界按第 4.8.2 节的 Sardinas–Patterson 条件使用。

`D5/S0/Computability/Coding/LengthProfileSeparation.lean` 的 `equal_lengths_unbounded_extension_gap (d r) (hr : 0 < r)` 中，将原参数改记为 $q,h$，避免把 $d$ 误当本章字母数。它比较二元码 $\{u0^h:|u|=q\}$ 与 $\{0^hu:|u|=q\}$，$h>0$：两者有 $2^q$ 个长度 $q+h$ 的词，完整长度多重集相同，Kraft 质量同为 $2^{-h}$，但其 `freeAt` 条件分别是 $q<n$ 与 $0<n$，最短可扩展深度分别为 $q+1$ 与一。这是长度数据不能决定可扩展位置的既有见证；本章受容量约束的完整切口及偏置最优值采用第 7.4–7.6 节的具体证明。

第 1.4.2–1.4.4 节已有完整回返块、未完成窗口与实际 roof 时间，第 1.4.7 节给出“每层一个”规则在换坐标后的双向反例。第 2.6.5 节的首两位交换保持 Haar 律，但需要运输读数 $q'_n=q_n\circ h^{-1}$ 与动力学 $S'=hSh^{-1}$ 才保持原接口；原生前缀查询不能仅凭同胚替换。第 4.7.9–4.7.11 节进一步区分完整窗口、共同律的推前、时钟和预算。这些关系在本章分别具体化为完整前缀、完整祖先束与式 (RST.31) 的不同成本单位。

定义 6.1.1的 $\mathcal C_b$、$S_\mu$ 与本章预算类及停止质量采用相同定义；只有共同律确为所指定的 iid $\mu_p$、合法类也相同时，才把 $M_b(\mu_p)$ 与定理 5.2.2 与定义 6.1.1 中在相同合法类上的 iid 容量记号对应。定理 6.1.2拥有无穷 iid 贪心取到性，推论 6.1.3拥有任意预算的均匀饱和定理；命题 7.3 仅需在那里分别代入 $b$ 与 $\widetilde b$。本章任意相关或原子 Borel 律的事件恒等式不依赖 iid 优化结论。适配 6.7.4–6.7.5 的有效概率接口另需实际共同参考柱的统一可计算名字、同一库存呈示、有效尾界，以及所用方向的正质量和全部查询局部供应；层列或运输预算可计算并不自动提供这些条件。

对全部后续实验的商接口，沿用第 1.3.6 节的具体关系接口及连接 6.7.6 的使用条件：必须在同一实际状态和历史、共同测试类上，有统一双向的合法测试翻译，保留拼接、更新、终端观察以及所指定的原始持续时间；成本若取可消去的交换幺半群中的可加值，还须保持该加法和成本读数。本章给出的逐路径停止事件、有标记策略和嵌套组合是这些条件的具体部分，不把无标记终端集合或一个最优数值等同于完整后续实验商。式 (RST.26) 对非负扩实期望只用逐点相等及积分；含无穷的加法不具可消去性，不能据此省去一般商接口的成本前提。

外部来源各承担下列范围：

1. [Stacks Project，Categories，Lemma 4.17.4，tag 002R](https://stacks.math.columbia.edu/tag/002R)，配合 [Definition 4.17.3，tag 09WP](https://stacks.math.columbia.edu/tag/09WP)，给出沿 initial functor 限制的极限同构。逆索引采用 $m\to n$ 当 $m\ge n$；保留深度包含函子为 initial，因为每个 $n$ 以上的保留层组成非空连通尾。数序中的余终性对应此反向索引中的 initial 性。该结果不含停止规则、预算、有效选点或等待费用；第 7.1 节分别证明坐标连续性和已给名字的有效转换。

2. Jean-Camille Birget，[Bernoulli measure on strings, and Thompson-Higman monoids](https://arxiv.org/abs/1004.5589v1)，§1.2，Lemmas 1.1–1.2，PDF 第 3 页。Lemma 1.1 的局部操作将 $x$ 换成 $xA^r$，保持均匀 Kraft 和；Lemma 1.2 对有限前缀码用有限次完整子节点展开／收缩刻画相同端集。这里每段有限，逐词局部展开对应 $r=m_S(|w|)-|w|$；无限码的结论另由不交柱并和非负求和承担。逐深度容量、禁止越过段边界的收缩及原成本不由该文的标量质量结论自动保证。任意共同律的守恒来自同一事件，不能只由同一 Kraft 数值推断。

3. François Coquet 与 Sandrine Toldo，[Convergence of values in optimal stopping and convergence of optimal stopping times](https://arxiv.org/abs/math/0504318v2)，Theorem 3，PDF 第 3 页。在固定有限视界、有界连续奖励、Skorokhod 概率收敛、Aldous 停止紧性及其规定的过滤包含或弱收敛条件下，该文给最优停止值收敛；证明中使用网格趋细。本文的上取层停止性由式 (RST.29) 直接证明。任意余终网格可以具有增长间距、无限视界和无界等待费，不能据此套用该值收敛结论或去掉逐深度容量限制。

4. Julio Backhoff-Veraguas、Daniel Bartl、Mathias Beiglböck 与 Manu Eder，[All Adapted Topologies are Equal](https://arxiv.org/abs/1905.00368v2)，Theorem 1.2、Theorem 1.3 与 Lemma 1.4，PDF 第 5–6 页。在固定有限步数和有界度量 Polish 状态空间下，文中比较适应 Wasserstein、对称因果 Wasserstein、信息、扩展弱及最优停止拓扑；无界度量版本另涉及 $p$ 阶矩及矩收敛。它解释为何决策时可用信息须进入运输结构，但不编码这里的 $b_n$、祖先束或无限视界均值。

5. Daniel Bartl、Mathias Beiglböck、Gudmund Pammer、Stefan Schrott 与 Xin Zhang，[The Wasserstein Space of Stochastic Processes in Continuous Time](https://arxiv.org/abs/2501.14135v1)，Definition 3.1，PDF 第 12 页；Propositions 4.3–4.4、Corollary 4.5，PDF 第 21–22 页。$\varepsilon$ 因果耦合可经条件分位数把一个停止时间运输成一族随机化策略，并给相应平均成本关系；$\varepsilon>0$ 时须保留构造中的终端截断，或限制原停止时刻加延迟不越过终端。具体地，在有限视界 $[0,H]$ 取含终点 $H$ 的网格，将最近完整记录的过滤记为 $\mathcal H_t=\mathcal F_{s(t)}$。若最大网格间隙不超过 $\varepsilon$，则在未越过终点的范围内有 $\mathcal H_t\subseteq\mathcal F_t\subseteq\mathcal H_{t+\varepsilon}$：右边来自下一网格点不晚于 $t+\varepsilon$。归一化到 $[0,1]$ 时相应缩放 $\varepsilon$，在终点使用文中的截断；若终点未保留，则不能自行声称该终端信息包含。条件分位数运输对随机化参数积分后比较成本，不保证每个参数的确定性策略都保持原费用。文中的 Hoover–Keisler 等价对应非前瞻、下有界成本的停止值等价；连续性还要求有界正则成本及连续的极限过程。一般随机化运输既不保证本章的确定性祖先束、逐深度字数，也不提供可逆的历史标记。

6. Akitoshi Kawamura 与 Stephen Cook，[Complexity Theory for Operators in Analysis](https://arxiv.org/abs/1305.0453v1)，校正版 §3.4.1、Lemma 3.9，PDF 第 13 页，以及 Definition 3.2。若输入表示的多项式时间翻译方向为 $\gamma'\to\gamma$，输出表示的方向为 $\delta\to\delta'$，则对 $\mathsf C=\mathsf{FP}$ 或 $\mathsf{FPSPACE}$ 有 $(\gamma,\delta)\text{-}\mathsf C\subseteq(\gamma',\delta')\text{-}\mathsf C$。先把新输入名字翻成旧输入名字，运行既有实现，再把旧输出名字翻成新输出名字，这正是该方向的组合。第 7.1 节只给可计算翻译；要进一步使用该复杂度结果，还须指定名字大小，并控制层列计算、投影、查询构造及响应处理。即使复杂度类相同，也不等于实际查询次数、等待时间或期望停止费用相等。

这些来源分别支撑标准组成部分；精确树切口、动态规划和等待判据按正文证明使用，不以文献类比替代约束核对。尚未给出的结论包括有用的整体多项式复杂度、仅可枚举输入上的一般有效选择、任意固定苛刻预算下的全律必要性、深度标记的比特最小性、改变源律后的策略等价，以及非均匀分支树、部分历史接口或任意增广过滤下的同样运输。本文不对综合的新颖性或新增形式认证作结论。

## 追加锚（本行以下为增补区）

## 8. 联合同余未来关系：精确状态商、布尔几何与恢复风险

固定一份合法动作语言，当前集合所需保留的结构由指定未来读数决定。精确计数要求联合直方图；只问是否非空时，最小合法删空证书反链承担相同的未来行为，两互素模数进一步化为七种规范形。把读数改为带误差的质量数据后，还必须分别声明来源总质量、估计器输出域和观测自身的共同来源条件，才能讨论最优恢复常数。

以下所有响应都按同一动作标签比较。剩余模数集合 $M$ 决定当前合法动作，已用模数集合 $U$ 决定开放协议中哪些新动作仍合法；同一个 LCM 不能替代这些控制信息。全体任意子集、概率直方图与某类实际历史的可达状态是不同来源域。数学结论按各节声明的域成立，不能把全域类数、自由质量锐常数或共同输入反例直接运输到未证明可达的来源类。

| 任务合同 | 精确结构或已确定的风险 |
|---|---|
| 固定有限 $M$，全部带标签精确计数 | $D=\operatorname{lcm}(M)$ 上的完整直方图及其闭合更新 |
| 同一动作合同，只观察是否非空 | 最小合法删空证书反链；两互素模数的七类规范形 |
| 两两互素模数，自由非负实质量，最大坐标误差 | 锐常数 $\kappa=\prod_i(2-1/(m_i-1))$ |
| 已知总质量的零和差 | 锐常数 $C_0=\kappa-\prod_i(1-1/(m_i-1))$ |
| 概率来源、实向量输出、任意逐格有界噪声 | 指定充分小噪声区间内风险 $C_0\varepsilon$ |
| 概率来源及概率输出，观测本身来自同一个概率来源 | 同一充分小噪声区间内风险 $C_0\varepsilon$；单模数有全尺度公式 |
| 单模数概率输出、任意逐格有界噪声 | 风险 $(1-1/m)\min(2\varepsilon,1)$，与上一行噪声合同不同 |

这里的常数针对质量读数的稳定性，不是布尔状态类数、样本复杂度或覆盖历史可达性。全部反事实响应是一份任务接口；数学上比较它们，不等于沿一条不可回退的实际删除轨迹免费取得它们。

### 8.1. 精确计数的联合直方图与最小状态

#### 8.1.1 对象、合法动作与带标签响应

固定正整数 $L$，置 $X_L=\mathbb Z/L\mathbb Z$。当前实际幸存集合是任意子集 $H\subseteq X_L$。剩余允许模数是有限集合
$$
M\subseteq\{m\in\mathbb N_{>0}:m\mid L\},
\qquad D=\operatorname{lcm}(M),\qquad\operatorname{lcm}(\varnothing)=1.
\tag{ER8.FH.1}
$$
因此 $D\mid L$。每个 $m\in M$ 最多使用一次；使用时可任选余数 $a\in\mathbb Z/m\mathbb Z$，删除 $a\bmod m$，随后从 $M$ 中移除 $m$。不要求必须使用所有模数，顺序任意，空续接也合法。

一条合法续接可由子集 $T\subseteq M$ 及各 $m\in T$ 的余数 $a_m$ 表示；删除交换，所以终态基数不依赖该子集的执行顺序。定义
$$
R_{T,a}(H)
=\#\{x\in H:\forall m\in T,\ x\not\equiv a_m\pmod m\}.
\tag{ER8.FH.2}
$$
特别地，$R_\varnothing(H)=|H|$。这里观察是**按动作标签索引的完整响应函数**，不是把所有读数丢掉标签后得到的无序多重集。

定义未来等价
$$
H\equiv_M H'
\quad\Longleftrightarrow\quad
\forall T\subseteq M\ \forall(a_m)_{m\in T},\quad
R_{T,a}(H)=R_{T,a}(H').
\tag{ER8.FH.3}
$$
全部中间读数已包含其中，因为每个前缀本身也是合法续接。若后续动作按已读基数自适应选择，同一 $M$ 下未来等价还使任一确定性策略的动作与读数轨迹相同：按执行步数归纳即可。这个说明不额外开放模数重用、未知新模数或非计数读数。

#### 8.1.2 完整直方图恰刻画未来等价

定义
$$
N_c(H)=\#\{x\in H:x\equiv c\pmod D\},
\qquad c\in\mathbb Z/D\mathbb Z.
\tag{ER8.FH.4}
$$

**定理 8.1（精确计数未来商）。** 在第 8.1.1 节协议下，对任意 $H,H'\subseteq X_L$，
$$
H\equiv_M H'
\quad\Longleftrightarrow\quad
\forall c\pmod D,\ N_c(H)=N_c(H').
\tag{ER8.FH.5}
$$

**充分性。** 因每个 $m\mid D$，一个点是否被任一允许类删除只取决于其模 $D$ 余数。故
$$
R_{T,a}(H)
=\sum_{c\bmod D}N_c(H)
  \prod_{m\in T}\bigl(1-\mathbf1_{c\equiv a_m\ (m)}\bigr).
\tag{ER8.FH.6}
$$
相同直方图给相同的全部读数。

**必要性。** 固定 $c\bmod D$。对每个 $T\subseteq M$，选择相容的余数 $a_m=c\bmod m$，记相应读数为 $R_T^c(H)$。则
$$
\boxed{N_c(H)=\sum_{T\subseteq M}(-1)^{|T|}R_T^c(H).}
\tag{ER8.FH.7}
$$
为验证，逐个 $x\in H$ 展开其在右侧的贡献。置 $I_m(x)=\mathbf1_{x\equiv c\ (m)}$，该贡献为
$$
\sum_{T\subseteq M}(-1)^{|T|}\prod_{m\in T}(1-I_m(x))
=\prod_{m\in M}\bigl[1-(1-I_m(x))\bigr]
=\prod_{m\in M}I_m(x).
$$
最后一个乘积为一，当且仅当每个 $m\in M$ 都整除 $x-c$，等价于 $D\mid x-c$。求和即得 ER8.FH.7。这里反演的是有限布尔格上的包含排除；不要求模数两两互素，也不把相容余数组合误当自由乘积。

每个 ER8.FH.7 所需查询都属于同一协议：各模数只用一次，选取任意子集，余数允许独立指定。相容余数特选是合法查询，不是对两个不同实现分别取最优值。未来读数相同遂逐格恢复相同 $N_c$，证毕。

边界也包含在证明中。$M=\varnothing$ 时 $D=1$，唯一格为 $|H|$，ER8.FH.7 只有空集项。模数 $1$ 可以在 $M$ 中：使用它会删尽，但协议仍允许不使用它。$L=1$、空集合和全体集合均不需排除。

#### 8.1.3 删除后的闭合更新与精度下降

设当前允许动作是 $(m,a)$，令
$$
H^+=\{x\in H:x\not\equiv a\pmod m\},\qquad
M^+=M\setminus\{m\},\qquad D^+=\operatorname{lcm}(M^+).
$$
有 $D^+\mid D$。新状态的完整直方图由旧状态唯一确定：
$$
\boxed{
N_r^+
=\sum_{\substack{s\bmod D\\s\equiv r\ (D^+)\\s\not\equiv a\ (m)}}N_s,
\qquad r\in\mathbb Z/D^+\mathbb Z.
}
\tag{ER8.FH.8}
$$
证明只是将新集合按旧模 $D$ 纤维分割：每个纤维或者全部保留、或者全部删除；保留纤维在模 $D^+$ 下合并。这给出交换关系
$$
\operatorname{hist}_{D^+}(H^+)
=\operatorname{Update}_{m,a}\bigl(\operatorname{hist}_{D}(H)\bigr).
\tag{ER8.FH.9}
$$
因此 $(M,(N_s)_{s\bmod D})$ 是确定性闭合接口；$L$ 可作为固定公共参数。当前基数为 $\sum_sN_s$，一次动作后的基数为 ER8.FH.8 各格之和。反复应用 ER8.FH.8 正好得到原集合逐次删除后的直方图，不产生近似误差。

**完整单步边缘公式。** 对任意 $d,m\mid L$，记
$$
K_d(b;H)=\#\{x\in H:x\equiv b\pmod d\},\qquad \ell=\operatorname{lcm}(d,m).
$$
若 $b\not\equiv a\pmod{\gcd(d,m)}$，两个类无交；若相容，令 $c\bmod\ell$ 为共同解，则
$$
K_d(b;H^+)=
\begin{cases}
K_d(b;H),&b\not\equiv a\pmod{\gcd(d,m)},\\
K_d(b;H)-K_\ell(c;H),&b\equiv a\pmod{\gcd(d,m)}.
\end{cases}
\tag{ER8.FH.10}
$$
这正是“更新边缘需要联合轮廓”的准确含义。当前任务需要的 $d\mid D$ 与 $m\in M$ 满足 $\ell\mid D$，所以 ER8.FH.4 已经供应该联合数；只保留若干单独边缘则未必闭合。

$D^+$ 可以严格小于 $D$。例如 $M=\{3,5\}$ 时 $D=15$；用掉模 $5$ 后只需模 $3$ 的直方图，再用掉模 $3$ 后只需基数。这是未来任务变少造成的精确合并，不是恢复已删除对象或抹去既有档案。如果未来重新开放已消费模数或新增测试，原合并不再自动合法。

仅保存 $D$ 不能恢复动作合法性。例如 $M_1=\{6\}$ 与 $M_2=\{2,6\}$ 都有 $D=6$，但动作模 $2$ 只在第二份状态合法。因此 $M$ 必须作为接口输入、公共控制状态或被保存的状态存在；本结论不要求把外部已经提供的同一信息重复计为内部记忆。

#### 8.1.4 最小性、商类数与可达范围

设摘要 $S(H)$ 能确定第 8.1.1 节全部精确未来响应。若 $S(H)=S(H')$，相同解码给出 $H\equiv_MH'$，由定理 8.1 得直方图相同。因此有唯一的因子
$$
\operatorname{im}S\longrightarrow
\operatorname{im}(\operatorname{hist}_D),\qquad
S(H)\longmapsto(N_c(H))_c.
\tag{ER8.FH.11}
$$
该因子满射。反向由 ER8.FH.6 与 ER8.FH.8，直方图本身达到充分性及闭合更新。所以这是指定读数与指定合法动作下的最粗精确状态商；不是对所有未来任务的绝对最小表示。

置 $q=L/D$。每个模 $D$ 纤维在 $X_L$ 中恰有 $q$ 个点，所以每格可取 $0,1,\ldots,q$。不同纤维互不相交，可以独立选取任意给定个数的点。因而全体 $H\subseteq X_L$ 的商类数恰为
$$
\boxed{\#(\mathcal P(X_L)/{\equiv_M})=(q+1)^D=(L/D+1)^D.}
\tag{ER8.FH.12}
$$
固定 $L,M$、无未计旁路且以固定长二进标签精确表示全部商类时，所需标签位数至少
$$
\left\lceil\log_2((L/D+1)^D)\right\rceil
=\left\lceil D\log_2(L/D+1)\right\rceil,
\tag{ER8.FH.13}
$$
按基数 $q+1$ 编码各格可达到该标签容量下界。它不计查询时间、更新位运算、输入表示或 $M$ 的额外编码费用。

若状态只来自某个受限历史类 $\mathcal R\subseteq\mathcal P(X_L)$，精确商类数是
$$
\#\{\operatorname{hist}_D(H):H\in\mathcal R\},
\tag{ER8.FH.14}
$$
不能直接套用 ER8.FH.12 的全域下界。比如只有一个可达集合时只需一个类。即使只限制固定总数 $|H|=h$，类数也变成多项式 $(1+z+\cdots+z^q)^D$ 的 $z^h$ 系数。若还要从“互异奇模数历史”取得下界，须先证明相应直方图确实可由那些历史实现。

当 $D=L$ 时每格只含一个点，直方图恰是 $H$ 的示性函数，确实没有状态压缩；当 $D<L$ 时只需保存纤维计数。例如 $L=30,M=\{3,5\}$ 有 $D=15$、$3^{15}$ 个类，而不是全部 $2^{30}$ 个集合。这个比较限当前有限动作域。

### 8.2. 改变协议时必须重算任务商

#### 8.2.1 空读数、终态、固定余数及动作标签

##### 8.2.1.1 省略空续接，仍观察精确基数

如果 $M$ 含某个 $m>1$，只看非空续接仍能恢复完整直方图。因为
$$
\sum_{a=0}^{m-1}R_{\{m\},a}(H)=(m-1)|H|.
\tag{ER8.FH.15}
$$
每个点恰在 $m-1$ 个余数选择下存活。右侧系数非零，故先恢复空续接基数，再应用 ER8.FH.7。

若 $M\subseteq\{1\}$，所有初态在这个删去空读数的协议下等价：$M=\varnothing$ 时没有查询，$M=\{1\}$ 时唯一非空动作总删尽。最小例是 $L=1,M=\{1\}$，$H=\varnothing$ 与 $H'=\{0\}$；非空续接读数都为零。

这里“非空续接”指至少执行一次动作，与第 8.2.1.4 节的“只问幸存集合是否非空”不是同一个任务。

##### 8.2.1.2 只观察完整用尽全部模数后的终态基数

余数仍全部允许，但不读中间状态。若 $1\notin M$，这一协议仍恢复模 $D$ 的完整直方图，无须模数互素。对任何 $T\subseteq M$ 固定余数 $a_T$，将所有未指定余数求和，得
$$
\sum_{(a_m)_{m\in M\setminus T}}R_{M,a}(H)
=\left(\prod_{m\in M\setminus T}(m-1)\right)R_{T,a_T}(H).
\tag{ER8.FH.16}
$$
对每个已经避开 $T$ 的点，每个剩余模数独立提供 $m-1$ 个不删除该点的余数选择；有限求和交换即证明等式。乘数非零，因此全部终值恢复全部部分续接读数，再用 ER8.FH.7。这里独立的是**查询余数的求和选项**，不是幸存点的余数分布。

$M=\varnothing$ 也包含在该结论中：唯一完整用尽协议就是空协议，$D=1$，只需总数。若 $1\in M$，全部终值恒为零，所有初态等价；若另额外保留初始基数，则只额外区分 $|H|$，仍不能一般恢复完整直方图。

##### 8.2.1.3 每个模数的余数预先固定

现为每个 $m\in M$ 固定一个 $a_m$，仅允许选择子集和顺序，包含空续接。定义命中签名及其单元计数
$$
\sigma(c)=\{m\in M:c\equiv a_m\pmod m\},\qquad
w_B(H)=\sum_{\substack{c\bmod D\\\sigma(c)=B}}N_c(H),\quad B\subseteq M.
\tag{ER8.FH.17}
$$
精确未来等价是全部 $w_B$ 相等；完整模 $D$ 直方图一般过细。确有
$$
R_T(H)=\sum_{B\cap T=\varnothing}w_B(H),\qquad
w_B(H)=\sum_{C\subseteq B}(-1)^{|B|-|C|}R_{M\setminus C}(H).
\tag{ER8.FH.18}
$$
第一式按签名分组，第二式是有限子集和的反演。这不是假定每个签名都有实现：无共同解的签名单元为空，其计数恒零。

令 $C_B=\{x\in X_L:\sigma(x\bmod D)=B\}$。在全体 $H$ 上，商类数为
$$
\prod_{B\subseteq M}(|C_B|+1).
\tag{ER8.FH.19}
$$
理由是这些实际单元分割 $X_L$，每个单元可以独立选任意数量的点。例：$L=3,M=\{3\},a_3=0$，$H=\{1\}$ 与 $H'=\{2\}$ 的全部固定余数读数都是一，模三直方图却不同。

**固定余数的全域分离判据。** 在每个模数最多提供一个固定余数测试的当前规则下，不论怎样预选余数，全部 $D$ 个余数的签名能够互相区分，当且仅当 $D\le2$。$D=1$ 由空读数处理；$D=2$ 必有模数二，其命中与未命中区分两格。

证明 $D>2$ 不可能分离全部格。取 $D$ 的最大素因子 $p$，写 $D=p^a t$、$(p,t)=1$。模 $D/p$ 的每个纤维有 $p$ 点。所有 $m\mid D/p$ 的测试在每条纤维内恒定；其他测试为 $m=p^a d$、$d\mid t$，每个测试在一条纤维内至多命中一点：若纤维点 $c+jD/p$ 与 $c+j'D/p$ 同时命中，则 $p^ad\mid(j-j')p^{a-1}t$，从 $d\mid t$ 和 $p\nmid t/d$ 得 $p\mid j-j'$，与 $0<|j-j'|<p$ 矛盾。若各点签名不同，每个纤维至少有 $p-1$ 个点被后一类测试命中，否则两个未命中点的全部签名相同。因此这些测试的总命中次数至少 $(p-1)p^{a-1}t$。

另一方面，每个可用模数只有一个固定类，即使加入全部 $p^a d$，总命中次数也至多
$$
\sum_{d\mid t}\frac{D}{p^a d}=\sum_{d\mid t}\frac td=\sigma_1(t).
$$
当 $p\ge3$，$t=1$ 时 $\sigma_1(t)/t=1<p-1$；$t>1$ 时所有素因子小于 $p$，故有限几何和给
$$
\frac{\sigma_1(t)}t
<\prod_{q\mid t,\ q\ \mathrm{prime}}\frac q{q-1}
\le\prod_{j=2}^{p-1}\frac j{j-1}=p-1.
$$
当 $p=2$，有 $t=1$ 且 $a\ge2$，于是 $\sigma_1(t)=1<2^{a-1}$。两种情形均与所需命中次数矛盾。故存在不同余数具有相同签名，以两个单点集合即得到计数协议的不可分离例。若开放同一模数的多个固定类，这个判据便不再适用：模三同时测试余数零和一，三个余数的签名已分别为“仅零”“仅一”“均否”，能够全部区分。

##### 8.2.1.4 只观察是否非空

将精确数值 $R_{T,a}(H)$ 换为布尔值 $\mathbf1_{R_{T,a}(H)>0}$ 后，直方图仍充分，但必要性失败。取
$$
L=3,\qquad M=\{3\},\qquad
H=\{0,1\},\qquad H'=\{0,2\}.
\tag{ER8.FH.20}
$$
初态都非空，每个合法删除动作最多移除一点，所以两份状态在全部允许续接后仍非空。它们布尔未来等价，但模三完整直方图不同；删除 $1\bmod3$ 后精确基数分别是一和二。

因此 ER8.FH.12–13 的精确计数下界不能转用于“最终能否删空”任务。该有限反例也没有证明任意无界奇模数布尔协议的完整分类。

##### 8.2.1.5 丢弃动作标签

若只保留所有读数的无序多重集，连任意余数协议也不够。$L=3,M=\{3\}$ 时，$H=\{0\}$ 与 $H'=\{1\}$ 的三个单步读数都是同一个多重集 $\{0,1,1\}$，加上初态读数仍相同。定理 8.1 比较的是对每个相同动作的读数，不能删掉这个对应关系。

#### 8.2.2 开放未用奇模数的精确计数协议

本节另行开放新模数。固定同一个奇正整数 $L$ 和已用有限奇模数集合 $U$；允许任意未用奇模数 $m>1$。动作需要先提升至 $\operatorname{lcm}(L,m)$，再删去一类，读数是这个**新 LCM 中的幸存基数**。

取一个共同奇数 $t\ge3$，使 $m=tL>\max(U\cup\{0\})$。于是 $m$ 合法、未用，且新 LCM 正是 $tL$。对每个 $a\in\{0,\ldots,L-1\}$，逐个旧点有 $t$ 个提升，删除 $a\bmod tL$ 恰删去旧类 $a\bmod L$ 的一个提升。因此
$$
C_a(H)=t|H|-\mathbf1_{a\in H}.
\tag{ER8.FH.21}
$$
空续接给 $|H|$，全部这些单步读数遂恢复每个示性位。所以在此强计数任务中，任意两个不同 $H,H'$ 都被一阶续接区分，固定 $L,U$ 的全域状态商就是整个 $\mathcal P(X_L)$。

即使省略空续接、仍读精确基数，也可由
$$
\sum_{a=0}^{L-1}C_a(H)=(tL-1)|H|
\tag{ER8.FH.22}
$$
先恢复总数，分母严格为正。$L=1$ 同样成立。

若只读是否非空，这一恢复论证不适用：对每个非空 $H$，ER8.FH.21 至少为 $(t-1)|H|>0$。这些严格增大分辨率的动作都不能首次删空，与原 TM.359 一致。不能把强任务的一阶无压缩结论称为 E7 布尔任务无压缩，更不能从全体任意 $H$ 的 $2^L$ 类直接推出受限可达历史有 $2^L$ 类。

第 8.1.2–8.1.4 节的有限 $M$ 模型还要求 $m\mid L$；本节刻意开放新模数并改变环境分辨率。两种协议的结论不冲突。例如有限 $M=\{2\},L=6$ 时，$\{0\}$ 与 $\{2\}$ 有相同模二直方图；若额外开放模三并删除零类，精确读数立即不同。这只说明改变未来动作集合就改变任务商。

#### 8.2.3 共同配对与操作结构不能由边缘或分层代替

**边缘相同不保证更新闭合。** 在模十五中取
$$
H_A=\{0,1\},\qquad H_B=\{6,10\}.
$$
两者模三直方图都是 $(1,1,0)$，模五直方图都是 $(1,1,0,0,0)$。删除 $0\bmod5$ 后，前者剩 $\{1\}$，后者剩 $\{6\}$；此时模三直方图分别为 $(0,1,0)$ 与 $(1,0,0)$。继续删除 $0\bmod3$，幸存基数分别是一与零。原边缘遗漏的是同一实际点的模三/模五配对，ER8.FH.10 所需的模十五联合格正好补齐它。

**相同分层不指定加法更新。** 群 $\mathbb Z/4$ 的链 $G\supset2G\supset0$ 与群 $(\mathbb Z/2)^2$ 的链 $G'\supset\{0\}\times\mathbb Z/2\supset0$，各有两个同构于 $\mathbb Z/2$ 的分层商；作为分次阿贝尔群，两者的 associated graded 都是两份 $\mathbb Z/2$。但前者有阶四元素，后者每个非零元素阶二，原群不相同。

更具体地，把模四数写成 $b_0+2b_1$。加一更新为
$$
(b_0,b_1)\longmapsto(1-b_0,\ b_1\mathbin\oplus b_0),
$$
而直积中加 $(1,0)$ 是 $(b_0,b_1)\mapsto(1-b_0,b_1)$。在 $(1,0)$ 上后继分别为 $(0,1)$ 与 $(0,0)$。这个经典扩张/进位区别说明“层的大小或抽象类型相同”不等于操作相同；它不是 定理 8.1 的证明，也不把任意 filtration 自动识别成整数余数塔。本稿的动态闭合由具体 ER8.FH.8/ER8.FH.10 承担。

### 8.3. 布尔任务的共同支持与删空证书

#### 8.3.1 固定动作合同与实际联合支持

固定正整数 $L$、当前实际幸存集合 $H\subseteq X_L=\mathbb Z/L\mathbb Z$，以及有限剩余模数集合

$$
M\subseteq\{m>0:m\mid L\},\qquad D=\operatorname{lcm}(M),\quad\operatorname{lcm}(\varnothing)=1.
\tag{ER8.FB.1}
$$

每个 $m\in M$ 至多使用一次，可任选 $a\in\mathbb Z/m\mathbb Z$，操作为删去 $a\bmod m$ 并消费这个模数。合法续接是一组动作

$$
C=\{(m,a_m):m\in T\},\qquad T\subseteq M,
$$

每个模数在 $C$ 中至多出现一次。动作带标签，包含空续接，允许中途停止。其读数为

$$
b_C(H)=\mathbf1\{\exists x\in H:\forall(m,a)\in C,\ x\not\equiv a\pmod m\}.
\tag{ER8.FB.2}
$$

未来等价定义为对所有同标签合法 $C$ 的读数相同。中间读数已经由各前缀查询包含；同一确定性自适应策略面对等价状态，也逐步取得相同动作及读数。这里没有开放重复模数、新模数、精确基数或额外的隐藏状态传感器。

令实际支持

$$
S_D(H)=\{r\in\mathbb Z/D\mathbb Z:K_D(r;H)>0\}.
\tag{ER8.FB.3}
$$

因为所有允许动作仅依赖模 $D$ 余数，ER8.FB.2 只依赖 $S_D(H)$。纤维中的点数及具体点身份可以遗忘。相同支持因此一定布尔等价，但不同支持也可能等价；下一节以后给出更粗的精确分类。

这一步使用同一个实际 $H$ 的联合支持。任意选择几份单模数支持再自由拼接，不能替代它。第 8.1 节的完整直方图仍充分，但其必要性所用的有符号反演不能用于布尔值。

当前动作后的实际支持仍可按共同来源计算。若执行 $(m,a)$，记

$$
M'=M\setminus\{m\},\qquad D'=\operatorname{lcm}(M'),
$$

则

$$
S_{D'}(H')=
\{r\bmod D':\exists s\in S_D(H),\ s\equiv r\pmod{D'},\ s\not\equiv a\pmod m\}.
\tag{ER8.FB.4}
$$

下面的商状态更新必须与这条实际更新相容，不能靠补入不存在的联合实现取得。

#### 8.3.2 完整用尽查询恢复部分查询

先假设每个 $m\in M$ 都大于1。对部分续接 $C$，有

$$
\boxed{
b_C(H)=\bigvee_{\substack{F\supseteq C\\F\text{ 对每个 }m\in M\text{ 恰选一个余数}}}b_F(H).
}
\tag{ER8.FB.5}
$$

证明：完整续接的幸存者必是部分续接的幸存者。反过来，若 $x$ 在 $C$ 后幸存，对每个未使用模数 $m$ 选择一个不同于 $x\bmod m$ 的余数即可；$m>1$ 保证这种选择存在，扩展后的完整续接仍保留同一个 $x$。

这里取存在的是**查询标签的扩展**，没有假设幸存点各坐标统计独立。ER8.FB.5 不要求模数互素，也不声称所有反事实查询可从一条不可回退的实际删除轨迹中免费取得。它只是等价关系和响应接口的数学识别。

若模数两两互素，CRT 将 $\mathbb Z/D\mathbb Z$ 双射为

$$
X=\prod_{m\in M}\mathbb Z/m\mathbb Z.
$$

将 ER8.FB.3 的同一支持写成 $S\subseteq X$。完整标签 $a=(a_m)$ 的读数为

$$
\boxed{
b_a(S)=\mathbf1\left\{S\cap\prod_{m\in M}
(\mathbb Z/m\mathbb Z\setminus\{a_m\})\ne\varnothing\right\}.
}
\tag{ER8.FB.6}
$$

因此完整任务是：支持是否与每个“一坐标删一个值”的补盒相交。它既不同于完整点集恢复，也不同于完整直方图恢复。

非互素时，点的联合像必须限制在 CRT 相容子集内。ER8.FB.5 仍成立，ER8.FB.6 则把 $S$ 视为该相容子集中的实际支持；不能宣称任意产品格点都由整数实现。

两个边界：$M=\varnothing$ 时只有当前是否非空，共两个类；若 $1\in M$，任何使用模数一的续接恒删空，所以可区分信息由 $M\setminus\{1\}$ 的查询供应。全用尽时恒为零，不能再用 ER8.FB.5 恢复部分读数。模数一仍须保留为合法控制动作，其执行将状态转为空。

#### 8.3.3 极小合法删空证书及闭合更新

把所有动作标签记为

$$
\mathcal A_M=\coprod_{m\in M}\{m\}\times\mathbb Z/m\mathbb Z.
$$

对每个 $r\in S_D(H)$，令

$$
E_r=\{(m,r\bmod m):m\in M\}.
$$

一份合法 $C\subseteq\mathcal A_M$ 删空，恰当且仅当它击中每个 $E_r$：

$$
b_C(H)=0\iff\forall r\in S_D(H),\quad C\cap E_r\ne\varnothing.
\tag{ER8.FB.7}
$$

所以这是有限超图的击中集关系，附加“一模数至多一个标签”的合法性约束。定义

$$
\mathcal K_M(S)=
\operatorname{Min}_{\subseteq}\{C:C\text{ 合法且 }b_C(S)=0\}.
\tag{ER8.FB.8}
$$

这是一份反链：只保留不可再删除动作的删空证书。有限性与合法性对子集封闭保证

$$
b_C(S)=0\iff\exists K\in\mathcal K_M(S),\quad K\subseteq C.
\tag{ER8.FB.9}
$$

因此两个支持布尔未来等价，当且仅当它们的 $\mathcal K_M$ 相同。该反链与全部布尔响应具有相同的核，因此它给出该任务的最粗精确状态商。一般目标族最小商接口列于第 8.10 节；以下另给实际证书表示和显式分类。

这份反链具有直接闭合更新。设执行 $e=(m,a)$，定义兼容筛选

$$
\mathcal K\downarrow e
=\{K\setminus\{e\}:K\in\mathcal K,
\ \forall(n,b)\in K,\ n=m\Longrightarrow b=a\}.
$$

即排除含有同模数冲突标签的旧证书，余下证书去掉已经执行的动作。则

$$
\boxed{
\mathcal K_{M'}(S_{D'}(H'))
=\operatorname{Min}_{\subseteq}(\mathcal K_M(S_D(H))\downarrow e).
}
\tag{ER8.FB.10}
$$

证明：对任意剩余合法 $T$，更新后删空等价于原来执行 $T\cup\{e\}$ 删空；由 ER8.FB.9 等价于某个旧极小证书包含在 $T\cup\{e\}$ 中。该证书不能使用冲突余数，其去掉 $e$ 后包含在 $T$ 中。反向同理，再取包含极小元得到精确反链。

若 $\mathcal K=\{\varnothing\}$，当前已空；若 $\mathcal K=\varnothing$，没有任何合法续接能删空，所有读数恒为一。不能只保存“存在删空证书”这个单一比特：标签和证书之间的包含关系控制下一步的成功与否。

反链表示不承诺一般情况下长度很小，也不承诺构造其所有成员的最优算法或复杂度。它给的是确切的有限关系和更新公式。

##### 8.3.3.1 具有唯一最大代表的闭包

令

$$
\operatorname{cl}_M(S)=
\left\{r\bmod D:\forall K\in\mathcal K_M(S),
\ \exists(m,a)\in K,\ r\equiv a\pmod m\right\}.
\tag{ER8.FB.11}
$$

则 $S\subseteq\operatorname{cl}_M(S)$，两者具有相同布尔未来，而且任何与 $S$ 等价的支持都包含在 $\operatorname{cl}_M(S)$ 中。因为每个旧删空证书也删空闭包，而支持包含关系给反向；任一等价支持中的点必须被所有旧极小证书击中。故每个布尔未来类有唯一的最大支持代表。为直接证明单调性，将闭包写成全部合法删空查询删除区域的交：$S\subseteq T$ 时，删空 $T$ 的查询是删空 $S$ 查询的子族，交的约束减少，故 $\operatorname{cl}_M(S)\subseteq\operatorname{cl}_M(T)$。闭包与原支持具有同一响应，再取闭包不变，所以幂等。空反链的交取全空间；含空证书时，其删除区域为空，闭包也为空。

这是相同测试关系两次取共同约束的标准闭包。最大代表是**行为的规范表示**，不表示实际 $H$ 增添了点，也不表示该最大代表来自允许的历史。真实来源、完整档案和强于布尔任务的其他读数仍需保留各自接口。

#### 8.3.4 单模数的精确分类

取 $M=\{m\}$、$m>1$，支持 $S\subseteq\mathbb Z/m\mathbb Z$。全部未来只有空动作或一次删除，精确分类为：

| 状态码 | 实际支持条件 | 极小删空证书 | 删除 $a$ 后 |
| --- | --- | --- | --- |
| `Empty` | $S=\varnothing$ | $\{\varnothing\}$ | 空 |
| `Point(r)` | $S=\{r\}$ | $\{\{(m,r)\}\}$ | 当且仅当 $a=r$ 为空 |
| `Many` | $\lvert S\rvert\ge2$ | 空反链 | 非空 |

各 `Point(r)` 由同标签 $a=r$ 区分；`Empty` 由空读数区分；`Many` 对全部删除仍为非空。这给恰好 $m+2$ 个类。`Many` 的最大支持代表是整个 $\mathbb Z/m\mathbb Z$，并不保留实际支持大小。

例如 $m=3$，$\{0,1\}$、$\{0,2\}$ 与 $\{0,1,2\}$ 都是 `Many`。这给出 ER8.FH.20 的完整单模数分类。

当 $L$ 是 $m$ 的任意正倍数时，分类相同：只看非空纤维数。模 $m$ 的一个支持格内可以有多个实际点，但仍是 `Point(r)`，不是 `Many`。最后一个模数消费后只需保留当前空／非空比特。

### 8.4. 两模数布尔几何、更新与实际历史反例

#### 8.4.1 两个互素模数的七类规范形

取 $M=\{m,n\}$，$m,n>1$ 且 $\gcd(m,n)=1$。记

$$
A=\mathbb Z/m\mathbb Z,\quad B=\mathbb Z/n\mathbb Z,
\quad S\subseteq A\times B.
$$

把 $S$ 看成二部图的边集。删除模 $m$ 余数 $a$ 是删掉一行，删除模 $n$ 余数 $b$ 是删掉一列。完整删空标签集合为

$$
Z(S)=\{(a,b):S\subseteq(\{a\}\times B)\cup(A\times\{b\})\}.
\tag{ER8.FB.12}
$$

这就是“一个左顶点加一个右顶点覆盖全部边”。ER8.FB.5 保证 $Z(S)$ 已决定所有部分续接，但下面还会把 $Z(S)$ 化成有限规范形，不要求保存 $mn$ 项表。

用 $R_a$、$C_b$ 分别表示删行和删列动作标签。分类如下；“规范支持”是 ER8.FB.11 的唯一最大代表：

| 规范类型 | 规范支持 | 极小删空证书反链 | 类数 |
| --- | --- | --- | ---: |
| 空 | $\varnothing$ | $\{\varnothing\}$ | 1 |
| 单点 $(r,s)$ | $\{(r,s)\}$ | $\{\{R_r\},\{C_s\}\}$ | $mn$ |
| 整行 $r$ | $\{r\}\times B$ | $\{\{R_r\}\}$ | $m$ |
| 整列 $s$ | $A\times\{s\}$ | $\{\{C_s\}\}$ | $n$ |
| 整十字 $(r,s)$ | $(\{r\}\times B)\cup(A\times\{s\})$ | $\{\{R_r,C_s\}\}$ | $mn$ |
| 两条不相交边 | $\{(r_1,s_1),(r_2,s_2)\}$，$r_1\ne r_2,s_1\ne s_2$ | $\{\{R_{r_1},C_{s_2}\},\{R_{r_2},C_{s_1}\}\}$ | $2\binom m2\binom n2$ |
| 整盒 | $A\times B$ | 空反链 | 1 |

所有行、列、单点等标签均保留原坐标意义；不能在没有运输实验标签的条件下把它们任意视为同一个状态。比如两种相反匹配的行列计数相同，但属于不同布尔未来类。

##### 8.4.1.1 分类的穷尽性

若 $S$ 为空、只有一条边、全部边位于一行或一列，前三种非空分类直接成立：同一行有至少两个不同列时，只有删掉那一行能够单步删空，其他一行一列组合也不能绕过它；列情形对称。

现在假设至少两行、两列有边。此时没有单步删空证书。若某个 $(a,b)\in Z(S)$，则至少有一条边在第 $a$ 行但不在第 $b$ 列，且至少有一条边在第 $b$ 列但不在第 $a$ 行。

任何第二个覆盖对 $(a',b')$ 都不能满足 $a'=a,b'\ne b$，否则旧列臂上的边无法被覆盖；也不能满足 $a'\ne a,b'=b$。故若第二个覆盖对存在，必须两坐标都不同。这时

$$
S\subseteq
\bigl[(\{a\}\times B)\cup(A\times\{b\})\bigr]
\cap
\bigl[(\{a'\}\times B)\cup(A\times\{b'\})\bigr]
=\{(a,b'),(a',b)\}.
\tag{ER8.FB.13}
$$

因为至少两行两列有边，两条边都必须存在。这个两边匹配恰有两份合法最小覆盖，已列在表中，不能再有第三份。

因此余下情况只有：$Z(S)$ 为空，对应整盒类；只有一个元素，对应整十字类；有两个元素，对应两条不相交边。全部七类得证。

每种规范支持都实际具有表中的证书反链；不同类型或不同标签给不同反链，故对应不同布尔未来类。互素 CRT 保证各规范支持都由模 $mn$ 子集实现；若 $mn\mid L$，在各支持纤维中各选一个点也可实现。因此在全体任意 $H\subseteq X_L$ 上，类数恰是

$$
\boxed{N_{m,n}=2+2mn+m+n+2\binom m2\binom n2.}
\tag{ER8.FB.14}
$$

这个数与纤维大小 $L/(mn)$ 无关。两模数反链至多含两个证书，每个至多含两个动作；表中每种形状都保留原坐标标签。固定长无旁路二进标签的容量下界为 $\lceil\log_2 N_{m,n}\rceil$，枚举七类可以达到标签容量，不包含初始化、查询和更新的位运算成本。当 $m=3,n=5$ 时，$N_{3,5}=100$，需7个标签位；$L=15$ 的强计数任务有32768类，需15位。

##### 8.4.1.2 从实际支持直接计算规范类型

扫描支持，先判断非空行列是否各只有一个；否则任选一条实际边 $(x_0,y_0)$。任意覆盖对必须满足 $a=x_0$ 或 $b=y_0$，因为它要覆盖这条边。

- 若删去第 $x_0$ 行后，剩余边的列支持只有一个 $b$，就得到候选 $(x_0,b)$；若列支持至少两个，则这一分支没有候选。
- 对称地，若删去第 $y_0$ 列后，剩余边的行支持只有一个 $a$，就得到候选 $(a,y_0)$。

在至少两行两列的前提下，两种剩余支持都非空，因此至多得到两个候选。零、一、两个候选分别确定整盒、整十字、两边匹配。过程中只需记录若干坐标代表及“零／一／至少二”标记；不用保存每格的计数。若输入是长度 $L$ 的成员表，可扫描这些实际点完成分类；此处只陈述一次扫描的结构，不给未核对的最优位复杂度。

非互素两模数仍可把实际联合支持视为二部图，七种证书形状的证明也仍适用，但支持只能取 CRT 相容边。最大代表须与相容像相交，某些类型或标签不可实现，不能继续宣称 ER8.FB.14 是其精确全域类数。

例如 $L=4,M=\{2,4\}$ 的实际联合像仅有四条相容边，其全部支持恰给 $16$ 个不同布尔类，而抽象 $2\times4$ 盒有 $36$ 类。证明前一数字不需枚举：先删除一种奇偶类，就只剩另一奇偶类的两个实际点；再分别删除这两点的模四标签，加上中途空／非空读数，能区别该两点支持的空、两个单点和双点四种可能。两种奇偶类分别如此，故全部 $4\cdot4=16$ 份支持都可区别。该论证仍使用同一实际支持及原动作标签。



#### 8.4.2 规范商的逐动作更新

删除行 $a$ 后，只剩模 $n$。将其单模数状态写成 `Empty`、`Point(s)`、`Many`，有：

| 原七类码 | 删除行 $a$ 后的单模数码 |
| --- | --- |
| 空 | `Empty` |
| 单点 $(r,s)$ | $a=r$ 时 `Empty`，否则 `Point(s)` |
| 整行 $r$ | $a=r$ 时 `Empty`，否则 `Many` |
| 整列 $s$ | `Point(s)` |
| 整十字 $(r,s)$ | $a=r$ 时 `Point(s)`，否则 `Many` |
| 匹配 $\{(r_1,s_1),(r_2,s_2)\}$ | $a=r_1$ 时 `Point(s_2)`；$a=r_2$ 时 `Point(s_1)`；其余为 `Many` |
| 整盒 | `Many` |

删除列 $b$ 后，只剩模 $m$，相应的完整表为：

| 原七类码（列动作） | 删除列 $b$ 后的单模数码 |
| --- | --- |
| 空（列动作） | `Empty` |
| 单点 $(r,s)$（列动作） | $b=s$ 时 `Empty`，否则 `Point(r)` |
| 整行 $r$（列动作） | `Point(r)` |
| 整列 $s$（列动作） | $b=s$ 时 `Empty`，否则 `Many` |
| 整十字 $(r,s)$（列动作） | $b=s$ 时 `Point(r)`，否则 `Many` |
| 匹配 $\{(r_1,s_1),(r_2,s_2)\}$（列动作） | $b=s_1$ 时 `Point(r_2)`；$b=s_2$ 时 `Point(r_1)`；其余为 `Many` |
| 整盒（列动作） | `Many` |

两方向的表由交换坐标相互对应。表中 `Many` 的使用依赖另一坐标集合至少有两个值，正是 $m,n>1$。在匹配情形，两保留列也不同。

这张表既可直接由规范支持计算，也可由 ER8.FB.10 消去动作得到。因为规范支持与原实际支持具有相同的全部带标签布尔响应，消费同一个动作后，余下全部响应继续相同；更新不能依赖被商掉的代表。再按第 8.3.4 节消去最后一个模数，即得到真实逐次删除的最终空／非空值。

规范“整列”并不声称原 $H$ 包含该列所有点；它只说明原支持在这份两动作任务中与整列行为等价。若下一轮重新允许已经用过的模数、增加新测试、要求计数或查历史，这份合并未必仍有效。

因此工作状态是 **剩余 $M$ 加相应规范码**。合法性不能由 $D$ 单独恢复，例如 $M=\{3,5\}$ 与 $M=\{15\}$ 都有 $D=15$，却允许不同的动作。若 $M$ 已由外部控制器提供，无须将同一信息再次计为内部记忆。

#### 8.4.3 同边缘而不同未来的实际前缀

完整联合直方图相同不可能给出不同布尔未来；它已经充分。这里反驳的是“总数与各单模数边缘计数已经足够”，并把反例写成实际同余删除历史，而非仅指定任意集合。

##### 8.4.3.1 模24的两个真实前缀

固定已用模数集合 $U=\{4,6,8,12,24\}$、剩余 $M=\{2,3\}$，每个模数各用一次。两份前缀删除的余数为：

| 已用模数 | 4 | 6 | 8 | 12 | 24 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 前缀 A 的余数 | 0 | 0 | 0 | 10 | 23 |
| 前缀 B 的余数 | 0 | 0 | 2 | 0 | 1 |

它们的共同 LCM 为24，直接删除后分别得到

$$
H_A=\{1,2,3,5,7,9,11,13,14,15,17,19,21\},
$$
$$
H_B=\{3,5,7,9,11,13,14,15,17,19,21,22,23\}.
$$

两者均有13个点，且

$$
\operatorname{hist}_2(H_A)=\operatorname{hist}_2(H_B)=(2,11),
\quad
\operatorname{hist}_3(H_A)=\operatorname{hist}_3(H_B)=(4,4,5).
\tag{ER8.FB.15}
$$

执行相同合法续接“删 $1\bmod2$，再删 $2\bmod3$”：前者先剩 $\{2,14\}$、继而为空；后者先剩 $\{14,22\}$、继而剩 $\{22\}$。因此当前总数、已用模数、剩余模数与两个边缘计数全部相同，布尔未来仍不同。按模二／模三坐标，前者具有中心 $(1,2)$ 的十字行为，后者属于整盒行为：前者的偶数点只占列二，后者的偶数点占列一与二，而两份奇数点均占满三列。

这份反例的前缀及续接都遵守有限、一模数一次、模数互异和大于1，但含有偶模数，**不是全奇 E7 前缀**。

##### 8.4.3.2 剩余模数可取3、5，但准备仍有偶模数

取 $L=120$，剩余 $M=\{3,5\}$。共同已用模数及两套余数如下：

| 模数 | 2 | 4 | 8 | 6 | 10 | 20 | 40 | 30 | 60 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 前缀 A | 1 | 2 | 4 | 2 | 2 | 8 | 24 | 10 | 36 |
| 前缀 B | 1 | 2 | 4 | 2 | 2 | 8 | 24 | 0 | 16 |

前七项共同保留 $\{0,16,40,96\}$，后两项分别给

$$
H_A=\{0,16\},\qquad H_B=\{40,96\}.
\tag{ER8.FB.16}
$$

二者的模3计数均为 $(1,1,0)$，模5计数均为 $(1,1,0,0,0)$。继续删 $0\bmod5$、$0\bmod3$ 后，前者剩 $\{16\}$，后者为空。它们在模15支持中分别是两个相反匹配，正是七类中的两个不同带标签匹配类。

这个实例证明即便**剩余动作全奇**，允许偶模数准备的状态仍可能需要真正的联合配对信息。它没有将该准备过程偷换成全奇前缀。

##### 8.4.3.3 严格互异奇模数可达性的边界

若某个 $H$ 确由有限互异、大于1的奇模数前缀产生，而一条合法、未重复模数的全奇有限续接使它为空，那么前缀和续接合并，已经给出了完整的有限互异奇模数整数覆盖。

所以，构造两个这种严格 E7 可达状态，并找一条共同合法全奇续接使它们的布尔读数不同，必然在其中一侧构造出 E7 的正解。当前不能把这个要求当成普通小反例任务而默默声称已满足。

反过来，**若**不存在有限互异奇模数覆盖，则所有严格 E7 可达前缀面对所有合法有限全奇续接，读数都恒为非空。给定同一控制域 $M$ 且可达状态域非空时，它们的布尔行为商将只有一个类。这是依赖开放命题的条件陈述，不是本稿证明了这一单类结果。

因此本稿全域的 $m+2$ 与 ER8.FB.14 类数不能直接用作 E7 可达状态下界。对任何已限定的可达集 $\mathcal R$，正确类数只是 $\#\{\mathcal K_M(S_D(H)):H\in\mathcal R\}$；该像必须另外分析。

### 8.5. 自由质量下的精确反演与锐误差常数

#### 8.5.1 共同线性数据与观察范数

取两两互素 $m_1,\ldots,m_r\ge2$，$D=\prod_i m_i$。CRT 将模 $D$ 的实际余数对应到 $X=\prod_i\mathbb Z/m_i\mathbb Z$。每个模数至多使用一次、每次任选一个余数删除，允许全部子集和顺序，保留动作标签。精确任务与直方图充分性见第 8.1 节；本节将整数计数线性扩展为非负实质量。

对实数直方图差 $z=(z_c)_{c\in X}$，定义
$$
R_{T,a}(z)=\sum_{c\in X}z_c\prod_{i\in T}(1-\mathbf1_{c_i=a_i}),
\qquad
\|z\|_{\rm obs}=\max_{T,a}|R_{T,a}(z)|.
$$
空续接给总质量差。这个观察函数确实定义范数：齐次性和三角不等式来自有限线性读数；观察为零时完整终态向量也为零，而第 8.5.2 节的矩阵可逆，故 $z=0$。差可以有符号；来源是两份非负有限质量直方图，没有额外承诺总质量相等，没有归一化成概率律。全部响应来自同一个 $z$，并非自由选择互不相容的边缘。

#### 8.5.2 完整删除读数的逆算子

令 $A_m=J_m-I_m$，其中 $J_m$ 是全一矩阵。使用全部模数后的读数向量为
$$
y=Az,\qquad A=\bigotimes_i A_{m_i}.
$$
直接相乘，利用 $J_m^2=mJ_m$，得到
$$
B_m=A_m^{-1}=\frac{J_m}{m-1}-I_m,\qquad
B=A^{-1}=\bigotimes_i B_{m_i}.
$$
单行绝对值之和为
$$
\kappa_m=\frac{m-2}{m-1}+(m-1)\frac1{m-1}
=2-\frac1{m-1}.
$$
张量积的每行绝对和相乘。因此
$$
\|B\|_{\infty\to\infty}=\kappa(M):=
\prod_i\left(2-\frac1{m_i-1}\right).
$$
完整终态读数属于全部续接读数，故
$$
\boxed{\|z\|_\infty\le\kappa(M)\|z\|_{\rm obs}.}
\tag{ER8.FC.1}
$$
这个界比直接对一个相容余数向量作 $2^r$ 项包含排除的误差估计更精确。

#### 8.5.3 全部中间读数下的同一锐见证

固定目标 $c^*\in X$，定义
$$
w_i(c)=
\begin{cases}2m_i-3,&c=c_i^*,\\-1,&c\ne c_i^*,\end{cases}
\qquad w=\bigotimes_i w_i.
$$
有 $\sum_c w_i(c)=m_i-2$，且
$$
\sum_{c\ne a_i}w_i(c)=
\begin{cases}-(m_i-1),&a_i=c_i^*,\\m_i-1,&a_i\ne c_i^*.\end{cases}
$$
于是
$$
|R_{T,a}(w)|=
\prod_{i\in T}(m_i-1)\prod_{i\notin T}(m_i-2)
\le t:=\prod_i(m_i-1).
$$
完整续接达到绝对值 $t$，而
$$
\|w\|_\infty=q:=\prod_i(2m_i-3),\qquad q/t=\kappa(M).
$$
因此 ER8.FC.1 在保留空续接和所有中间读数的观察范数中也精确。所有响应由同一明确整数向量产生，已经满足全部联合约束。

空模数族采用空乘积一，唯一读数是总数，常数一。模数二的因子恰为一；若有 $r$ 个互异奇素数，每个因子至少 $3/2$，故 $\kappa(M)\ge(3/2)^r$。这只描述计数反演的数值稳定性。

#### 8.5.4 足够大共同周期中的实际集合实现

取 $L=qD$。每个模 $D$ 纤维含 $q$ 个点，故可选取两份实际集合 $H,H'\subseteq\mathbb Z/L\mathbb Z$，满足
$$
N_c(H)=\max(w_c,0),\qquad
N_c(H')=\max(-w_c,0).
$$
所需计数均不超过 $q$，不同纤维互不相交，可以逐格选点。正负支持不交，因而两集合也可选为不交；该构造选择一个足够大的共同周期，不保证任意预先指定周期的纤维容量足够。两直方图差为 $w$，全部计数响应的最大差为 $t$，目标格差为 $q$。

全部 $m_i$ 为奇数时 $q,D,L$ 也为奇数。不过，这只证明两集合的共同有限实现，没有证明它们是互异奇模数覆盖历史的可达前缀；不能据此声称该受限可达类也有相同最坏常数。

例如 $m_1=3,m_2=5,c^*=(0,0)$：$D=15,q=21,t=8,L=315$。目标格差21，另4格差−3，另2格差−7，剩8格差1。两集合基数29与26；空续接差3，只用模3时绝对差6，只用模5时绝对差4，完整用尽时绝对差8。因此常数为 $21/8$。

#### 8.5.5 有界误差与自由质量 minimax

完整终态观测满足 $\|\widehat y-y\|_\infty\le\varepsilon$ 时，线性反演给
$$
\|\widehat x-x\|_\infty\le\kappa(M)\varepsilon,
\qquad \widehat x=B\widehat y.
$$
这对非负实直方图成立。在总质量未固定、每格无固定上界的该来源类中，任何恢复算法都不能改进此最坏常数：取足够大的共同非负基线 $b$，令
$$
x^\pm=b\pm\varepsilon w/t.
$$
两份实际完整响应的中点，与两者各自全部读数的距离都不超过 $\varepsilon$，但目标格相差 $2\kappa(M)\varepsilon$。同一个观测输入下，任何算法至少对其中一份来源有误差 $\kappa(M)\varepsilon$。没有假设独立噪声或概率噪声律。可以明确取共同基线 $b_c=\varepsilon|w_c|/t$，非负性随即逐格成立。

将来源类和估计器量词完整写出，令 $F(x)$ 是全部带标签读数，$\mathcal A$ 输出实向量，则
$$
\inf_{\mathcal A}\sup_{x\in\mathbb R_{\ge0}^X}
\sup_{\|\eta\|_\infty\le\varepsilon}
\|\mathcal A(F(x)+\eta)-x\|_\infty=\kappa\varepsilon.
$$
若输出必须非负，反演后逐格截到 $[0,\infty)$ 不增加对非负真值的误差，所以公式仍成立。若还限制完整观测必须等于同一个非负来源的精确响应，下界中的 $F(b)$ 已满足该条件，上界沿用反演，故自由质量合同下也保持同一值。这两项扩展仍未施加总质量一的约束。

若实际直方图为整数且已知 $\kappa(M)\varepsilon<1/2$，逐格舍入可精确恢复。若另给固定总质量、受限可达类、已知直方图上界，或只观察非空与否，最优常数必须重新检验；本节没有证明这些更小来源类也达到该常数。测量样本数、查询成本与位复杂度另计。

### 8.6. 已知总质量：零和锐常数及概率来源

#### 8.6.1 来源、零和约束与精确常数

取有限两两互素整数 $m_1,\ldots,m_r\ge2$，$D=\prod_i m_i$，并经 CRT 将实际模 $D$ 余数写为 $X=\prod_i\mathbb Z/m_i\mathbb Z$。每个模数至多用一次，每次任选一个余数删除，保留动作标签，允许全部子集、顺序和空续接。

对同一实向量 $z\in\mathbb R^X$，定义
$$
R_{T,a}(z)=\sum_{c\in X}z_c\prod_{i\in T}\mathbf1_{c_i\ne a_i},
\qquad \|z\|_{\rm obs}=\max_{T,a}|R_{T,a}(z)|.
$$
本题新增的条件是 $\sum_cz_c=0$。定义 $C_0(M)$ 为满足
$$
\|z\|_\infty\le C_0(M)\|z\|_{\rm obs}\quad
\text{对所有 }\sum_cz_c=0
\tag{ER8.CM.2}
$$
的最小非负常数。空族时只有一个坐标，唯一零和向量为零，故按此定义 $C_0(\varnothing)=0$。这避免把不存在的非零向量比值当成一个最大值。

固定总质量下的精确误差放大常数为
$$
\boxed{
C_0(M)=\prod_{i=1}^r\left(2-\frac1{m_i-1}\right)
-\prod_{i=1}^r\left(1-\frac1{m_i-1}\right).
}
\tag{ER8.CM.1}
$$


以下用同一个零和向量满足全部观察约束，并以修正逆行的绝对系数和给匹配上界。仅浮点优化值或仅终态见证不足以承担这两项义务。

#### 8.6.2 在零和子空间上修正逆行

记
$$
t=\prod_i(m_i-1),\qquad
q=\prod_i(2m_i-3),\qquad
h=\prod_i(m_i-2),\qquad
\kappa=q/t.
$$
完整使用全部模数的读数 $y$ 满足
$$
y=Az,\qquad A=\bigotimes_i(J_{m_i}-I_{m_i}),\qquad
B=A^{-1}=\bigotimes_i\left(\frac{J_{m_i}}{m_i-1}-I_{m_i}\right).
$$
每个状态点属于恰好 $t$ 个完整删除试验，因此
$$
\sum_a y_a=t\sum_cz_c=0.
\tag{ER8.CM.3}
$$

先假定所有 $m_i\ge3$，固定目标 $c^*$。逆矩阵对应行记作 $b_a=B_{c^*,a}$，有
$$
b_a=\frac1t\prod_i
\begin{cases}-(m_i-2),&a_i=c_i^*,\\1,&a_i\ne c_i^*.
\end{cases}
$$
全部 $b_a$ 非零，且任何正项均至少为 $1/t$。由 ER8.CM.3，可从这一行的每个系数减去 $1/t$ 而不改变零和向量的恢复：
$$
z_{c^*}=\sum_a\left(b_a-\frac1t\right)y_a.
\tag{ER8.CM.4}
$$
对正负项分别计算，
$$
\left|b_a-\frac1t\right|=|b_a|-\frac1t\operatorname{sgn}(b_a).
$$
行绝对和为 $\sum_a|b_a|=q/t$，符号和也分解为单坐标乘积：
$$
\sum_a\operatorname{sgn}(b_a)
=\prod_i((m_i-1)-1)=h.
$$
所以修正逆行的绝对系数和恰为
$$
\sum_a\left|b_a-\frac1t\right|=\frac{q-h}{t}.
$$
目标 $c^*$ 任意，完整读数又包含在全部观察中，故得到 ER8.CM.2，常数为 $(q-h)/t$。

若某个 $m_i=2$，则 $h=0$。此时直接使用原逆矩阵的行绝对和 $q/t$ 即得同一个上界；不能在这一分支照搬“所有正项至少为 $1/t$ 且无零项”的上述计算。空族 $q=h=t=1$，结论为零，单独已处理。

#### 8.6.3 达到全部观察上界的共同零和向量

沿用目标 $c^*$，定义
$$
w_i(c)=\begin{cases}2m_i-3,&c=c_i^*,\\-1,&c\ne c_i^*,\end{cases}
\qquad w=\bigotimes_iw_i,
\qquad
\nu=w-h\delta_{c^*},\quad v=\nu/t.
\tag{ER8.CM.5}
$$
因为 $\sum_cw_c=h$，$\nu$ 和 $v$ 都是零和向量。目标格为
$$
v_{c^*}=\frac{q-h}{t}.
$$

核对全部中间读数，而非只核对终态。令
$$
g_T=\prod_{i\notin T}\frac{m_i-2}{m_i-1},
\qquad \rho=h/t=\prod_i\frac{m_i-2}{m_i-1}.
$$
若某个被选的删除余数等于对应目标余数，则目标点被删除，$R_{T,a}(\delta_{c^*})=0$，并且
$$
R_{T,a}(v)=(-1)^{|\{i\in T:a_i=c_i^*\}|}g_T,
\qquad |R_{T,a}(v)|\le1.
$$
若全部选定余数均不等于目标余数，则目标点保留，原张量响应为正，
$$
R_{T,a}(v)=g_T-\rho.
$$
由于 $0\le\rho\le g_T\le1$，该读数也在 $[0,1]$ 内。空续接属于后一情形，读数恰为零。

当 $r\ge1$，完整使用全部模数并至少删除一次目标余数时，$g_T=1$，目标点已删除，故绝对读数为一。因此
$$
\|v\|_{\rm obs}=1,\qquad
v_{c^*}=(q-h)/t.
$$
结合上界自动得到 $\|v\|_\infty=(q-h)/t$，证明该常数确实最小。一个 $v$ 同时承担零总量、全部带标签读数和目标误差，没有组装不相容的边缘或分别取得的极值。

几个直接后果：单模数的常数始终为一；含模数二时固定总量完全不降低自由质量的锐常数，因为原 $w$ 已经零和；其余非空族下降量为 $h/t\in(0,1)$。对 $r$ 个互异奇素数，
$$
C_0(M)=\kappa-h/t\ge(3/2)^r-1.
$$
给定总量没有消除这套计数反演的指数增长。这仍只是此观察协议内的稳定性结论。

#### 8.6.4 非负概率来源与实向量输出的局部风险

零和向量不是虚构来源差。任意非零零和向量 $z$ 的正负质量相等，记为 $s>0$，则 $z/s$ 恰为两个概率直方图 $z^+/s$ 和 $z^-/s$ 的差。由于 ER8.CM.2 齐次，ER8.CM.1 也是概率直方图两两比较的精确 Lipschitz 常数。

现在给定真实来源 $p\in\Delta_X=\{p\ge0:\sum_cp_c=1\}$，全部读数附加任意逐坐标绝对值不超过 $\varepsilon$ 的确定性噪声。估计器输出域在本节明确为 $\mathbb R^X$，无需输出本身是概率直方图。定义
$$
\mathcal R_{\mathbb R^X}(\varepsilon)=
\inf_{\mathcal A}\sup_{p\in\Delta_X}
\sup_{\|\eta\|_\infty\le\varepsilon}
\|\mathcal A(F(p)+\eta)-p\|_\infty,
\qquad F(p)=(R_{T,a}(p))_{T,a}.
$$

若所有 $m_i\ge3$，由已知完整读数满足 $\sum_a y_a=t$，目标坐标的仿射恢复式是
$$
\widehat p_c=1+\sum_a\left(B_{c,a}-\frac1t\right)\widehat y_a.
\tag{ER8.CM.6}
$$
每行误差至多 $C_0\varepsilon$。若有模数二，直接用 $B\widehat y$ 得到同一界。因此对任意 $\varepsilon\ge0$，
$$
\mathcal R_{\mathbb R^X}(\varepsilon)\le C_0\varepsilon.
$$

给出可实现的局部下界尺度。令
$$
P=\prod_i(3m_i-4).
$$
因为 $\sum_c|w_c|=P$，且从正的目标格减去 $h$ 不改变其符号，
$$
\|v\|_1=\frac{P-h}{t}.
$$
非空族有 $P-h>0$。对
$$
0\le\varepsilon\le\varepsilon_0:=\frac{t}{P-h},
\tag{ER8.CM.7}
$$
取任意固定概率向量 $p_0$，例如 $\delta_{c^*}$，并构造
$$
b=\varepsilon|v|+(1-\varepsilon\|v\|_1)p_0,
\qquad p^\pm=b\pm\varepsilon v.
$$
$b,p^+,p^-$ 均逐格非负，且总质量皆为一。共同输入 $F(b)$ 与两份来源的每条读数分别相差 $\mp\varepsilon F(v)$，绝对值均不超过 $\varepsilon$。同时
$$
\|p^+-p^-\|_\infty=2C_0\varepsilon.
$$
同输入的两点误差界使任何估计器至少在一侧有误差 $C_0\varepsilon$。故
$$
\boxed{\mathcal R_{\mathbb R^X}(\varepsilon)=C_0\varepsilon
\quad(0\le\varepsilon\le t/(P-h)).}
\tag{ER8.CM.8}
$$
这是充分的统一局部区间，不主张它是最大区间。共同观测本身来自合法归一化来源 $b$，所以要求观测内部相容也保留该下界。空模数族下概率来源唯一，风险恒为零。若允许内部随机化且以期望最大坐标损失计风险，上述共同输入的两点下界也成立：对每个随机输出先用三角不等式，再取期望，至少一份固定来源的期望误差达到同一下界。确定性上界仍可使用，因此这一局部实输出公式不变。

若进一步要求估计器输出仍在 $\Delta_X$，本节任意逐格有界噪声合同下的构造只给出同一个下界：其估计器类更小。ER8.CM.6 不保证输出总和一；普通截断或归一化也没有被证明不增加最大坐标误差。单模数概率输出结果 ER8.SO.1 给出全尺度风险 $(1-1/m)\min(2\varepsilon,1)$；当 $m>2$ 且 $0<\varepsilon\le1/2$，它严格大于实向量输出风险 $\varepsilon$。因此概率输出普遍保留 ER8.CM.8 等式的断言已被否定，一般多模数组合在任意逐格有界噪声合同下的概率输出风险仍未在此求出。要求观测本身完全自洽是另一个更强的合同，下文单独处理。

#### 8.6.5 同基数实际有限集合的实现

以下取非空模数族。空族的零和向量只有零，所得两集合均为空；它不提供非零锐比值或归一化概率见证。

$\nu=w-h\delta_{c^*}$ 是零和整数向量，各格绝对值不超过 $q$。取共同周期 $L=qD$，每个模 $D$ 纤维有 $q$ 个点，可以逐纤维选择两实际集合 $H,H'\subseteq\mathbb Z/L\mathbb Z$，使其直方图分别为 $\nu^+$ 和 $\nu^-$。两集合基数相同：
$$
|H|=|H'|=(P-h)/2.
$$
该值为整数，因为 $P$ 与 $h$ 同奇偶。全部响应差来自同一对集合，观察范数为 $t$，目标格差为 $q-h$。取相同基数归一化后仍达到相同的比值。

这是存在一个足够大共同周期的实际实现；不证明预先指定的每个 $L$ 都能容纳该向量。全部模数为奇数时 $q,D,L$ 也为奇数，但没有证明这两集合可由互异奇模数覆盖历史产生。整数性、给定周期容量以及历史可达性均须另行核对。

对 $(3,5)$，$D=15,q=21,h=3,t=8,P=55,L=315$。目标格差从自由质量的 21 降为 18，其他格仍为四个 $-3$、两个 $-7$ 和八个 $1$。可取 $|H|=|H'|=26$；空续接差零，只用模三的峰值六，只用模五的峰值四，完整续接峰值八。因此锐比值为 $18/8=9/4$。

### 8.7. 任意逐格有界噪声与概率输出的全尺度风险

#### 8.7.1 单模数来源、输出和噪声合同

固定 $m\ge2$，未知来源 $p$ 在概率单纯形 $\Delta_m$ 内。删除余数 $i$ 后的精确剩余质量为 $y_i=1-p_i$，空操作质量为一。观察每格有任意确定性噪声，$|\widehat y_i-y_i|\le\varepsilon$；空读数同样可带界内噪声，但总质量一是事先给定的合同。全部观测不要求恰好属于某个合法来源的无噪声像。

估计器也必须输出一个概率向量。则最坏坐标误差的 minimax 风险恰为
$$
\boxed{\mathcal R_{\Delta_m}(\varepsilon)
=\left(1-\frac1m\right)\min\{2\varepsilon,1\}.}
\tag{ER8.SO.1}
$$
这里对每个已知半径 $\varepsilon\ge0$，定义
$$
\mathcal R_E(\varepsilon)=\inf_{\mathcal A:\,\operatorname{input}\to E}
\sup_{p\in\Delta_m}\sup_{\|\eta\|_\infty\le\varepsilon}
\|\mathcal A(F(p)+\eta)-p\|_\infty,
\qquad F(p)=(1,1-p_1,\ldots,1-p_m).
$$
输出域 $E$ 分别取 $\Delta_m$ 或 $\mathbb R^m$。总质量一是已知条件，不是靠带噪空读数重新估计。它不同于任意实向量输出时的 $\min\{\varepsilon,1/2\}$。特别地，对 $m\ge3$ 和 $0<\varepsilon\le1/2$，要求输出仍是概率律使风险严格大于 $\varepsilon$。

#### 8.7.2 概率单纯形内的共同中心界

设非空紧集 $K\subseteq\Delta_m$ 在最大坐标范数中的直径不超过 $w$。记各格极值 $l_i=\min_{p\in K}p_i$、$u_i=\max_{p\in K}p_i$，所以 $u_i-l_i\le w$。取
$$
r=\frac{m-1}{m}w,\qquad
\alpha_i=\max\{0,u_i-r\},\qquad
\beta_i=l_i+r.
$$
有 $\alpha_i\le\beta_i$，因为 $2r\ge w$。还满足
$$
\sum_i\alpha_i\le1\le\sum_i\beta_i.
\tag{ER8.SO.2}
$$
右侧：选 $p\in K$ 达到某一坐标 $l_j$，其余坐标至多 $l_i+w$，于是 $1\le\sum_i l_i+(m-1)w=\sum_i\beta_i$。

左侧：令 $S=\{i:u_i>r\}$，$k=|S|$。$S$ 为空时直接成立；否则选 $j\in S$ 和达到 $u_j$ 的 $p\in K$。每个其他 $i\in S$ 有 $u_i\le p_i+w$，故
$$
\sum_i\alpha_i=\sum_{i\in S}(u_i-r)
\le1+(k-1)w-kr
=1+\left(\frac{k}{m}-1\right)w\le1.
$$
由 ER8.SO.2 可在每个区间 $[\alpha_i,\beta_i]$ 内选 $q_i$，使总和一；从所有下界起，按固定次序补足总量即可。$q\ge0$ 且总和一，自动属于 $\Delta_m$。对所有 $p\in K$，有 $u_i-r\le q_i\le l_i+r$，因此 $\|p-q\|_\infty\le r$。

这个构造给出一个对整个可能来源集共同有效的中心。它不是对任意外部实向量进行截断或归一化，也没有声称存在保持所有真值距离的非扩张归一化映射。

#### 8.7.3 全部噪声尺度的上界与有效估计器

对可实现的观测 $\widehat y$，其可能来源集
$$
K(\widehat y)=\{p\in\Delta_m:\ |1-p_i-\widehat y_i|\le\varepsilon\ \forall i\}
$$
非空且紧。空读数若超出其合法噪声区间则整个输入不可实现，不影响最坏风险；可实现时没有另加的来源限制。

同一可能来源集内任意两点的每格距离至多 $2\varepsilon$，概率格又在 $[0,1]$ 内，因此直径至多 $w=\min\{2\varepsilon,1\}$。使用第 8.7.2 节共同中心，得到 ER8.SO.1 的上界。不可实现输入上任意输出固定概率律，使估计器在整个输入域有定义。

此估计器可有效计算：可能来源集是逐格区间与总和一的交。先令
$$
L_i=\max\{0,1-\widehat y_i-\varepsilon\},\qquad
U_i=\min\{1,1-\widehat y_i+\varepsilon\}.
$$
各区间非空且 $\sum_iL_i\le1\le\sum_iU_i$ 当且仅当该集合非空。必要性由求和得到，充分性由从全部下界开始按固定次序填充得到。可行时，其精确格极值为
$$
l_i=\max\left\{L_i,1-\sum_{j\ne i}U_j\right\},\qquad
u_i=\min\left\{U_i,1-\sum_{j\ne i}L_j\right\}.
$$
按 ER8.SO.2 的固定顺序填充构造即可。格极值公式来自剩余质量必须能装入其他格的区间；连续区间和的填充保证这两个端点都能达到。这里有效性以读数和噪声半径的精确可操作表示为前提；不把任意不可计算实数默认当成有限输入。

#### 8.7.4 共同输入下的多来源匹配下界

先设 $0\le\varepsilon\le1/2$。令 $b_i=(1-2\varepsilon)/m$，构造 $m$ 个实际概率来源
$$
p^{(j)}=b+2\varepsilon e_j,\qquad1\le j\le m.
$$
使用同一个观测
$$
\widehat y_i=1-b_i-\varepsilon,
$$
空读数取一。对来源 $p^{(j)}$，第 $j$ 格噪声是 $+\varepsilon$，其他格噪声是 $-\varepsilon$，均合法。任意概率输出 $q$ 必有某个 $q_j\le1/m$，于是针对来源 $p^{(j)}$ 有
$$
\|p^{(j)}-q\|_\infty
\ge b_j+2\varepsilon-q_j
\ge2\varepsilon\left(1-\frac1m\right).
$$
当 $\varepsilon\ge1/2$，使用全部顶点来源 $e_j$ 和完整读数 $\widehat y_i=1/2$，噪声只需 $1/2$。任意概率输出同样至少对一个顶点有误差 $1-1/m$。这与上界匹配，证明 ER8.SO.1。

若允许内部随机化并以期望最大坐标误差计风险，同一公式仍成立。对共同输入的随机概率输出 $Q$，存在固定索引 $j$ 使 $\mathbb E Q_j\le1/m$；针对该固定来源，对逐坐标下界取期望即可。实输出的两点下界则对逐点三角不等式取期望。对抗者无需看到已经实现的随机种子再选择来源。

#### 8.7.5 输出域和观测相容性的独立作用

如果允许估计器输出任意实向量，逐格取 $1-\widehat y_i$ 给误差至多 $\varepsilon$；常向量 $(1/2,\ldots,1/2)$ 给误差至多 $1/2$。上述共同来源族中任选不同两点，相距 $\min\{2\varepsilon,1\}$，给两点下界的一半。因此
$$
\mathcal R_{\mathbb R^m}(\varepsilon)=\min\{\varepsilon,1/2\}.
$$
对于 $m=2$ 两种风险相同；对于 $m>2$，差异来自共同输入需同时容纳 $m$ 个来源，而输出受总质量限制，不能只用两点构造判断全部输出约束。

另一方面，上面小噪声下界的完整读数一般不是某个概率来源的精确响应：
$$
\sum_i(1-\widehat y_i)=1+(m-2)\varepsilon.
$$
若另要求观测本身完整自洽，即 $\widehat y_i=1-\widetilde p_i$ 对某个 $\widetilde p\in\Delta_m$，直接输出 $\widetilde p$ 即得误差至多 $\varepsilon$。因此 ER8.SO.1 的严格放大不能运输到这个更小的噪声输入类。第 8.7 节采用任意逐格有界噪声，不能在证明下界时暗中切换两种合同。

#### 8.7.6 与多模数固定质量结果的关系

单模数的零和反演 Lipschitz 常数为一。本稿不否定这一精确事实，也不否定实向量输出的小噪声 minimax 等式。它说明“来源必须归一化”与“输出也必须归一化”是两个不同条件；仅有来源两两差异的锐常数，未自动完成受约束输出的风险证明。

多模数、全部联合续接在任意逐格有界噪声合同下的概率输出风险仍需另行研究。这里已经给出对“所有模数组合都保持实向量输出风险”这一断言的单模反例，以及该反例族在全噪声尺度上的准确解答。没有证明任何极端概率来源来自互异奇模数覆盖前缀。

### 8.8. 观测自身来自同一个概率来源时的风险

#### 8.8.1 一般多模数的自洽局部风险

保持真实来源 $p\in\Delta_X$、全部带标签的部分及完整读数 $F(p)$ 和已知总质量一。现在额外要求观测本身是某个合法概率来源的精确响应：
$$
\widehat y=F(\widetilde p),\qquad \widetilde p\in\Delta_X,\qquad
\|\widehat y-F(p)\|_\infty\le\varepsilon.
$$
这是对同一个完整观测施加共同来源约束，比仅要求存在真实来源及逐格合法噪声更强。空读数自动为一；各部分读数也必须属于同一个 $\widetilde p$，不是分别存在来源。

取完整读数子向量 $\widehat y^{\rm full}$，使用完整逆矩阵输出
$$
\mathcal A(\widehat y)=B\widehat y^{\rm full}=\widetilde p.
$$
该输出自动非负且总质量一。由于 $\widetilde p-p$ 零和，ER8.CM.2 给出
$$
\|\mathcal A(\widehat y)-p\|_\infty
\le C_0(M)\|F(\widetilde p)-F(p)\|_\infty
\le C_0(M)\varepsilon.
$$
这同时适用于含模数二的分支，无需假定对任意外部实向量存在不扩张的归一化映射。合法观测域外可任意输出固定概率律，使估计器处处有定义。

下界沿用 ER8.CM.7 中同一个 $b,p^+,p^-$。在 $0\le\varepsilon\le t/(P-h)$ 内，它们都是概率来源，共同观测 $F(b)$ 本身满足这里的自洽合同，且两侧所有完整、部分及空读数的噪声仍由同一个 $F(v)$ 控制。两来源相距 $2C_0(M)\varepsilon$，因此任何概率输出估计器至少在一侧产生误差 $C_0(M)\varepsilon$。结合自动概率输出的上界，对非空模数族得到
$$
\boxed{
\mathcal R_{\Delta_X}^{\rm consistent}(\varepsilon)
=C_0(M)\varepsilon,\qquad
0\le\varepsilon\le\frac{t}{P-h}.
}
\tag{ER8.CM.9}
$$
这里的风险与 ER8.CM.8 使用相同的最坏坐标误差，只把输出域改为 $\Delta_X$ 并将输入限制为上述自洽观测。空模数族的概率来源唯一，风险恒为零。

单模数时，ER8.CM.9 给出 $0\le\varepsilon\le1/2$ 上的自洽观测概率输出风险 $\varepsilon$。ER8.SO.1 中 $m>2$ 时的严格放大属于任意逐格有界噪声合同，其共同下界观测不属于这里的自洽输入类。ER8.CM.9 不延伸至该更大的噪声类，也不确定超出给定充分半径后的全尺度风险。

#### 8.8.2 单模数自洽观测的全尺度精确公式

设 $m\ge2$，真实来源为 $p\in\Delta_m$，全部删除读数为 $F(p)_i=1-p_i$，空读数恒为一。观测必须由同一个概率来源产生，即 $\widehat y=F(a)$、$a\in\Delta_m$，并满足 $\|F(a)-F(p)\|_\infty=\|a-p\|_\infty\le\varepsilon$。允许任意确定性估计器；其输入中的 $a$ 可由 $1-\widehat y$ 精确恢复。风险是对一切合法 $(a,p)$ 的最大坐标误差上确界，再对估计器取下确界。

在这个合同下，概率输出与实向量输出的全尺度风险分别为

$$
\boxed{R_{\Delta_m}^{\rm consistent}(\varepsilon)
=\min\left(\varepsilon,1-\frac1m\right),
\qquad
R_{\mathbb R^m}^{\rm consistent}(\varepsilon)
=\min(\varepsilon,1/2).}
\tag{ER8.CS.1}
$$

**概率输出上界。** 直接输出实际观测来源 $a$ 给误差至多 $\varepsilon$；恒输出均匀来源 $u=(1/m,\ldots,1/m)$ 给误差至多 $1-1/m$。按已知半径选择二者较优者，便得到 ER8.CS.1 的第一项上界。这不要求把一个任意非相容向量归一化。

**概率输出下界。** 令 $h=\min(\varepsilon,1-1/m)$。固定共同观测来源为同一个 $a=u$。对每个 $j\in\{1,\ldots,m\}$，定义

$$
p_i^{(j)}=
\begin{cases}
1/m+h,&i=j,\\
1/m-h/(m-1),&i\ne j.
\end{cases}
\tag{ER8.CS.2}
$$

由 $0\le h\le(m-1)/m$，全部 $p^{(j)}$ 非负且总质量一。它们与同一观测来源 $u$ 的最大坐标距离均为 $h\le\varepsilon$，所以所有来源都与同一个合法完整观测 $F(u)$ 相容。

任意概率输出 $q$ 至少有一个坐标 $q_j\le1/m$。对相应的实际来源 $p^{(j)}$，误差至少为 $p_j^{(j)}-q_j\ge h$，从而得到匹配下界。这里多个来源共享一个输入；没有按真实来源分别选择观测或估计器。

**实向量输出。** 输出 $a$ 或恒输出 $(1/2,\ldots,1/2)$ 给上界 $\min(\varepsilon,1/2)$。反向令 $s=\min(\varepsilon,1/2)$，取同一观测来源 $a=(1/2,1/2,0,\ldots,0)$，以及两个来源

$$
p^+=(1/2+s,1/2-s,0,\ldots,0),\qquad
p^-=(1/2-s,1/2+s,0,\ldots,0).
$$

两者与 $a$ 的距离为 $s$，相互距离为 $2s$。对同一个观测 $F(a)$，三角不等式使任意实向量输出至少在一侧产生误差 $s$，完成证明。

允许内部随机化、并以期望最大坐标误差计风险也不改变两式：概率输出下界使用某个固定 $j$ 满足 $\mathbb E Q_j\le1/m$，对该固定来源取期望；实输出下界对逐点三角不等式取期望。无需让对抗者看到随机种子后选择来源。

与任意逐格有界噪声合同的对照是

| 观测合同 | 实向量输出风险 | 概率输出风险 |
|---|---|---|
| 任意逐格有界噪声，观测自身不必有共同来源 | $\min(\varepsilon,1/2)$ | $(1-1/m)\min(2\varepsilon,1)$ |
| 观测自身来自同一个概率来源 | $\min(\varepsilon,1/2)$ | $\min(\varepsilon,1-1/m)$ |

第一行由 ER8.SO.1 及其匹配上、下界给出；第二行由上文直接证明。两种观测合同的真实来源类相同，都允许概率单纯形的边界点。若要求真实来源和观测来源的所有坐标严格正，但没有统一的正下界，可以对边界构造同时取
$$
p_\delta=(1-\delta)p+\delta u,\qquad
 a_\delta=(1-\delta)a+\delta u,\qquad0<\delta<1.
$$
它们均严格正，观测距离及共同输入下的分离下界同时缩为 $1-\delta$ 倍，仍满足原半径。令 $\delta\downarrow0$ 得到相同风险上确界；不能说边界顶点在该较小域内实际取到。零噪声直接恢复；若另指定固定正坐标下界，则是未在这里求出的新合同。

对于 $m>2$，自洽观测在 $0\le\varepsilon\le1/2$ 内确实消除概率输出相对于实输出的风险增量，但在 $\varepsilon>1/2$ 后仍存在严格增量。因此“共同实现消除全部输出约束代价”也是过强结论。共同实现改变可行输入集合，概率输出改变可行中心集合；两个条件须分别保留。

ER8.CS.1 补全 ER8.CM.9 的单模数全尺度风险；一般多模数全尺度风险、覆盖历史可达性和计算复杂度不由它推出。

### 8.9. 有限算法、精确证书与数值实例

#### 8.9.1 直方图反演、更新及协议变体

有限整数 $L$、完整列表 $M$、余数标签及 $H$ 的有限成员表足以计算全部对象；LCM、余数归类和有限整数求和都是精确运算。初始直方图可扫描 $L$ 个位置取得；给定旧 $D$ 格计数，ER8.FH.8 可一次扫描这些格，跳过被删格并加到新格，使用至多 $D$ 次筛选和累加。上述是算术操作计数，没有把余数运算或大整数运算视为免费的位复杂度结果。若只有未来响应 oracle，ER8.FH.7 提供至多 $D2^{|M|}$ 个带标签查询的直接恢复方法，不主张查询最优。

对任意正整数 $L$、有限 $M\subseteq\{m>0:m\mid L\}$ 和实际集合 $H\subseteq X_L$，从完整带标签响应恢复直方图与执行合法删除可交换。具体地，令 $\mathcal I_M$ 为 ER8.FH.7 的反演，执行 $(m,a)$ 后令 $M'=M\setminus\{m\}$、$D'=\operatorname{lcm}(M')$，则
$$
\mathcal I_{M'}\bigl((R_{T,b}(H^+))_{T\subseteq M',\,b}\bigr)
=\operatorname{Update}_{m,a}
 \bigl(\mathcal I_M((R_{T,b}(H))_{T\subseteq M,\,b})\bigr)
=\operatorname{hist}_{D'}(H^+).
$$
这里 $\operatorname{Update}_{m,a}$ 正是 ER8.FH.8。证明是：ER8.FH.6 与 ER8.FH.7 在实际响应像和可实现直方图之间互逆；剩余续接 $T$ 在删除后的响应，等于原集合先执行 $(m,a)$ 再执行 $T$ 的响应；ER8.FH.8–ER8.FH.9 因而给出上式。沿任意合法动作词归纳，反演后的状态递推始终等于同一实际集合的逐次删除。这包括空 $M$、模数一及非互素组合，不要求扩大来源域或补入不存在的联合格。改变空读数、终态读数、预定余数或新模数的许可时，须采用第 8.2 节各自的协议及边界。

#### 8.9.2 布尔规范形、最大代表与实际后继

在完整二部乘积支持域上，全部支持数为 $2^{mn}$，布尔类数由 ER8.FB.14 给出。下表保留不同盒大小的具体结果。

| 两坐标大小 | 全部支持数 | 布尔类数 |
| --- | ---: | ---: |
| $2\times2$ | 16 | 16 |
| $2\times3$ | 64 | 25 |
| $3\times2$ | 64 | 25 |
| $2\times4$ | 256 | 36 |
| $3\times3$ | 512 | 44 |
| $2\times5$ | 1024 | 49 |
| $3\times4$ | 4096 | 69 |
| $3\times5$ | 32768 | 100 |
| $4\times4$ | 65536 | 114 |

这些是抽象二部盒大小。非互素或重复大小的行仍是图论实例，不声称它们来自两个互素不同整数模数。七类码、最大代表、完整到部分的布尔恢复和第 8.4.2 节的两方向更新均由前述证明适用于每份实际支持。

对任意 $m\ge2$ 及其正倍数 $L$，单模数任务在全部 $H\subseteq X_L$ 上恰有 $m+2$ 个行为类。模 $m$ 的全部 $2^m$ 份支持均可实现，而第 8.3.4 节将它们分成空支持、各带标签单点及至少两格非空三种形态；最后一种形态只有一个行为类。不同协议各自取商。

对任意正整数 $L$、有限 $M\subseteq\{m>0:m\mid L\}$ 及 $H\subseteq X_L$，ER8.FB.7–ER8.FB.11 给出实际联合支持的删空关系、合法证书更新和唯一最大等价支持。后者等于全部同类支持之并：每份同类支持都包含在闭包中，闭包本身又与原支持等价。空 $M$、模数一和非互素组合均由这些定义处理；完整到部分的恢复 ER8.FB.5 另要求每个模数大于一。若来源限于历史类 $\mathcal R$，其商类数是实际像 $\#\{\mathcal K_M(S_D(H)):H\in\mathcal R\}$，最大等价支持则不保证可由该历史类达到。

第 8.4.3 节的两组真实前缀给出相同边缘与不同后继，其准备包含偶模数。上述分类和更新不确定最优算法复杂度，也不供应严格互异奇模数历史的可达性。

#### 8.9.3 自由质量反演的有理实例

自由质量的数值实例使用同一个删除算子 $F$、逆矩阵 $B$ 与张量 $w$；其恒等式为 $AB=BA=I$、$\|Fw\|_{\rm obs}=t$ 及 $\|w\|_\infty=q$。

对 $(3,5)$，模 $315$ 的两份实际来源基数为 $29$ 与 $26$，按空、模三、模五、完整续接分组的差响应峰值为 $3,6,4,8$，目标格差为 $21$，所以锐常数为 $21/8$。所有 $24=(1+3)(1+5)$ 个合法标签读数都属于同一对来源。

对第 8.5 节任意有限两两互素模数族及任意实向量 $z$，逐因子的逆矩阵恒等式给 $BF^{\rm full}(z)=z$，部分响应则仍由同一个 $F(z)$ 决定。对任意 $\varepsilon\ge0$，取 $b=\varepsilon|w|/t$ 与 $x^\pm=b\pm\varepsilon w/t$，两来源逐格非负；第 8.5.3 节的全部响应界给 $\|F(x^\pm)-F(b)\|_\infty\le\varepsilon$，而 $\|x^+-x^-\|_\infty=2\kappa\varepsilon$。这给出与同一个合法输入相容的来源对，且适用于空模数族约定。

整数来源还有两种不同的充分恢复办法：$\kappa\varepsilon<1/2$ 保证反演后逐格舍入精确；若每条真读数本身为整数，则 $\varepsilon<1/2$ 也可先舍入完整读数再精确反演。两者都不应冒称为所有受限整数来源的最优阈值。

#### 8.9.4 固定质量的轨道降维与有理原始—对偶证书

固定质量的有理证书可在目标格稳定群下平均。逐坐标置换全部非目标余数，得到每个坐标“等于目标／不等于目标”的 $2^r$ 个轨道。平均保留目标格与总量，并将响应写成原响应的凸组合，故不增加观察范数。因此目标格的最优值等于这个轨道子空间上的最优值。

轨道编号为 $\beta\in\{0,1\}^r$，零表示目标，一表示非目标，按字典序排列。每格取值记为 $x_\beta$，轨道权为 $w_\beta=\prod_i(m_i-1)^{\beta_i}$。协议编号 $\alpha\in\{0,1,2\}^r$ 分别表示省略、删除目标、删除一个非目标；其轨道计数因子 $f_i(\alpha_i,\beta_i)$ 三行依次为 $(1,m_i-1)$、$(0,m_i-1)$、$(1,m_i-2)$。令 $F_\alpha(x)=\sum_\beta x_\beta\prod_i f_i(\alpha_i,\beta_i)$。原始问题是最大化 $x_{(0,\ldots,0)}$，条件为 $\sum_\beta w_\beta x_\beta=0$ 及全部 $|F_\alpha(x)|\le1$。可消去目标坐标 $x_0=-\sum_{\beta\ne0}w_\beta x_\beta$ 得有限有理线性规划；最优性由下面的可行向量及对偶恒等式证明，不依赖采用哪一种求解算法。

| 模数族 | 固定总量常数 $C_0$ | 自由总量常数 $\kappa$ | ER8.CM.7 的共同充分半径 |
|---|---:|---:|---:|
| $(3,5)$ | $9/4$ | $21/8$ | $2/13$ |
| $(2,3)$ | $3/2$ | $3/2$ | $1/5$ |
| $(3,7)$ | $7/3$ | $11/4$ | $3/20$ |
| $(3,5,7)$ | $9/2$ | $77/16$ | $6/115$ |

其中 LP 可返回不同最优见证。例如 $(2,3)$ 的一份 LP 证书可归一化至半径 $1/3$，ER8.CM.5 的规范张量见证给统一半径 $1/5$；二者的锐常数均为 $3/2$。这里的半径表示把该见证方向嵌入概率来源的允许尺度，不是任意噪声下概率输出风险的上界。表中始终使用 ER8.CM.5 的同一规范构造及其统一半径，未混用不同见证。完整 LP 数据保留每格轨道值及非零对偶系数。

下面列出 $2\le m_i\le9$ 中全部严格递增、两两互素且长度至多三的模数族，再加 $(2,3,5,7)$，共 $47$ 族（含空族）。每族使用模 $D$ 的同一个 $v=\nu/t$，正质量为 $(P-h)/(2t)$，规范充分半径为 $t/(P-h)$。空族不作这个除法。模 $315$ 的等基数来源各有 $26$ 点，全部 $24$ 条响应属于同一对来源。

七份有理证书的轨道值与非零对偶系数列在本节；空族及单坐标边界分别保留。ER8.CM.1 与 ER8.CM.8 的任意参数结论仍由第 8.6 节的直接对偶恒等式、共同见证与非负归一化证明承担。

##### 8.9.4.1 七份有理最优性证书

对协议 $\alpha$ 中的每个非目标删除，平均所有 $m_i-1$ 个实际非目标标签，所得原坐标响应记为 $\overline F_\alpha$。原坐标 $c$ 的保留因子 $g_i(\alpha_i,c_i)$ 依次为 $1$、$\mathbf1_{c_i\ne0}$，以及当 $c_i=0$ 时为 $1$、当 $c_i\ne0$ 时为 $(m_i-2)/(m_i-1)$。这里把目标平移到零。因而 $\overline F_\alpha(c)=\prod_i g_i(\alpha_i,c_i)$，平均后的读数仍受原观察范数控制。

下面每份证书满足
$$
\sum_\alpha\lambda_\alpha\overline F_\alpha(c)
=\mathbf1_{c=0}+\mu,
\qquad \sum_\alpha|\lambda_\alpha|=C_0.
\tag{ER8.LP.1}
$$
将此恒等式乘以任意零和输入 $z_c$ 后求和，即得 $z_0\le C_0\|Fz\|_{\rm obs}$；改变符号给绝对值上界。表中原始轨道向量满足全部响应约束且 $x_0=C_0$，故达到上界。$s_+$ 是归一化轨道向量的正质量 $\sum_\beta w_\beta\max(x_\beta,0)$；非零向量的概率嵌入半径为 $1/(2s_+)$。

| 证书／模数族 | 轨道值 $x_\beta$ | 轨道权 $w_\beta$ | $C_0$ | $\kappa$ | $s_+$ | 该向量半径 | $\mu$ | 非零 $\alpha:\lambda_\alpha$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| LP1 $()$ | $(0)$ | $(1)$ | $0$ | $1$ | $0$ | 不定义 | $-1$ | $\varnothing$ |
| LP2 $(2)$ | $(1,-1)$ | $(1,1)$ | $1$ | $1$ | $1$ | $1/2$ | $-1$ | $(1):-1$ |
| LP3 $(3)$ | $(1,-1/2)$ | $(1,2)$ | $1$ | $3/2$ | $1$ | $1/2$ | $-1$ | $(1):-1$ |
| LP4 $(3,5)$ | $(9/4,-3/8,-7/8,1/8)$ | $(1,4,2,8)$ | $9/4$ | $21/8$ | $13/4$ | $2/13$ | $-1$ | $(1,1):1/4; (1,2):-1; (2,1):-1$ |
| LP5 $(2,3)$ | $(3/2,-1/2,-1/2,0)$ | $(1,2,1,2)$ | $3/2$ | $3/2$ | $3/2$ | $1/3$ | $0$ | $(2,1):-1/2; (2,2):1$ |
| LP6 $(3,7)$ | $(7/3,-1/4,-11/12,1/12)$ | $(1,6,2,12)$ | $7/3$ | $11/4$ | $10/3$ | $3/20$ | $-1$ | $(1,1):1/3; (1,2):-1; (2,1):-1$ |
| LP7 $(3,5,7)$ | $(9/2,-7/16,-11/16,1/16,-77/48,7/48,11/48,-1/48)$ | $(1,6,4,24,2,12,8,48)$ | $9/2$ | $77/16$ | $115/12$ | $6/115$ | $-1$ | $(1,1,1):-1/3; (1,1,2):1/4; (1,2,1):1/3; (1,2,2):-1; (2,1,1):7/12; (2,1,2):-1; (2,2,1):-1$ |

**证书的直接证明。** 空族的零和输入只有零，取 $\mu=-1$、空对偶和即得恒等式，风险也为零。单模数二的向量 $(1,-1)$、单模数三的向量 $(1,-1/2)$ 都零和，全部删除响应的绝对值至多一；$-\overline F_{(1)}(c)=\mathbf1_{c=0}-1$ 给其对偶式。

对表中各个全由 $m_i\ge3$ 组成的多模数族，原始向量正是 ER8.CM.5 的 $v=\nu/t$，全部部分响应的可行性已经由第 8.6.3 节的两个分支证明。对全用尽协议 $\alpha\in\{1,2\}^r$，定义 $I(\alpha)=\{i:\alpha_i=1\}$。平移后的逆矩阵行减去 $1/t$，再将具有同一轨道类型的标签相加，其系数为
$$
\lambda_\alpha=
\frac{(-1)^{|I(\alpha)|}\prod_{i\in I(\alpha)}(m_i-2)-1}{t}
\prod_{i\notin I(\alpha)}(m_i-1),
\qquad \mu=-1.
\tag{ER8.LP.2}
$$
这是表中全部非零系数的统一公式：全用尽响应求和等于 $t\sum_c z_c$，所以移心减去的项在原坐标恰为总质量，给 ER8.LP.1。行绝对和是第 8.6.2 节证明的 $C_0$。表中 $(3,5)$、$(3,7)$、$(3,5,7)$ 的原始向量和对偶系数因此由一般证明同时认证，而非从各自独立的最优边缘拼接。

$(2,3)$ 的替代向量为 $(3/2,-1/2,-1/2,0)$，轨道权为 $(1,2,1,2)$，总和为零。九个轨道协议按 $00,01,02,10,11,12,20,21,22$ 排列时，响应依次为
$$
(0,-1,1/2,-1/2,0,-1/2,1/2,-1,1).
\tag{ER8.LP.3}
$$
故全部真实标签读数的绝对值至多一（该向量在非目标标签置换下不变）。对偶只有 $\lambda_{21}=-1/2,\lambda_{22}=1$，$\mu=0$：第一坐标非目标时两项皆零；第一坐标为目标而第二坐标非目标时为 $-1/2+1/2=0$；两坐标均为目标时为一。这逐原坐标证明 ER8.LP.1。正质量为 $3/2$，允许半径为 $1/3$；规范张量向量的正质量为 $5/2$，仅给统一半径 $1/5$。不同向量供应相同 $C_0=3/2$，不供应一个已经证明最大的局部区间。


##### 8.9.4.2 规范固定质量的全部参数实例

下表的 $q,t,h,P$ 与第 8.6 节相同；$s_+=(P-h)/(2t)$ 是 $v=\nu/t$ 的正质量，$Q=\prod_i(1+m_i)$ 是包括空查询的合法部分标签数。每条公式来自同一规范向量；表中 $\varepsilon_0$ 均为充分半径。

| 模数族 | $D$ | $q$ | $t$ | $h$ | $P$ | $C_0$ | $s_+$ | $\varepsilon_0$ | $Q$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| F01 $()$ | $1$ | $1$ | $1$ | $1$ | $1$ | $0$ | $0$ | 不定义 | $1$ |
| F02 $(2)$ | $2$ | $1$ | $1$ | $0$ | $2$ | $1$ | $1$ | $1/2$ | $3$ |
| F03 $(3)$ | $3$ | $3$ | $2$ | $1$ | $5$ | $1$ | $1$ | $1/2$ | $4$ |
| F04 $(4)$ | $4$ | $5$ | $3$ | $2$ | $8$ | $1$ | $1$ | $1/2$ | $5$ |
| F05 $(5)$ | $5$ | $7$ | $4$ | $3$ | $11$ | $1$ | $1$ | $1/2$ | $6$ |
| F06 $(6)$ | $6$ | $9$ | $5$ | $4$ | $14$ | $1$ | $1$ | $1/2$ | $7$ |
| F07 $(7)$ | $7$ | $11$ | $6$ | $5$ | $17$ | $1$ | $1$ | $1/2$ | $8$ |
| F08 $(8)$ | $8$ | $13$ | $7$ | $6$ | $20$ | $1$ | $1$ | $1/2$ | $9$ |
| F09 $(9)$ | $9$ | $15$ | $8$ | $7$ | $23$ | $1$ | $1$ | $1/2$ | $10$ |
| F10 $(2,3)$ | $6$ | $3$ | $2$ | $0$ | $10$ | $3/2$ | $5/2$ | $1/5$ | $12$ |
| F11 $(2,5)$ | $10$ | $7$ | $4$ | $0$ | $22$ | $7/4$ | $11/4$ | $2/11$ | $18$ |
| F12 $(2,7)$ | $14$ | $11$ | $6$ | $0$ | $34$ | $11/6$ | $17/6$ | $3/17$ | $24$ |
| F13 $(2,9)$ | $18$ | $15$ | $8$ | $0$ | $46$ | $15/8$ | $23/8$ | $4/23$ | $30$ |
| F14 $(3,4)$ | $12$ | $15$ | $6$ | $2$ | $40$ | $13/6$ | $19/6$ | $3/19$ | $20$ |
| F15 $(3,5)$ | $15$ | $21$ | $8$ | $3$ | $55$ | $9/4$ | $13/4$ | $2/13$ | $24$ |
| F16 $(3,7)$ | $21$ | $33$ | $12$ | $5$ | $85$ | $7/3$ | $10/3$ | $3/20$ | $32$ |
| F17 $(3,8)$ | $24$ | $39$ | $14$ | $6$ | $100$ | $33/14$ | $47/14$ | $7/47$ | $36$ |
| F18 $(4,5)$ | $20$ | $35$ | $12$ | $6$ | $88$ | $29/12$ | $41/12$ | $6/41$ | $30$ |
| F19 $(4,7)$ | $28$ | $55$ | $18$ | $10$ | $136$ | $5/2$ | $7/2$ | $1/7$ | $40$ |
| F20 $(4,9)$ | $36$ | $75$ | $24$ | $14$ | $184$ | $61/24$ | $85/24$ | $12/85$ | $50$ |
| F21 $(5,6)$ | $30$ | $63$ | $20$ | $12$ | $154$ | $51/20$ | $71/20$ | $10/71$ | $42$ |
| F22 $(5,7)$ | $35$ | $77$ | $24$ | $15$ | $187$ | $31/12$ | $43/12$ | $6/43$ | $48$ |
| F23 $(5,8)$ | $40$ | $91$ | $28$ | $18$ | $220$ | $73/28$ | $101/28$ | $14/101$ | $54$ |
| F24 $(5,9)$ | $45$ | $105$ | $32$ | $21$ | $253$ | $21/8$ | $29/8$ | $4/29$ | $60$ |
| F25 $(6,7)$ | $42$ | $99$ | $30$ | $20$ | $238$ | $79/30$ | $109/30$ | $15/109$ | $56$ |
| F26 $(7,8)$ | $56$ | $143$ | $42$ | $30$ | $340$ | $113/42$ | $155/42$ | $21/155$ | $72$ |
| F27 $(7,9)$ | $63$ | $165$ | $48$ | $35$ | $391$ | $65/24$ | $89/24$ | $12/89$ | $80$ |
| F28 $(8,9)$ | $72$ | $195$ | $56$ | $42$ | $460$ | $153/56$ | $209/56$ | $28/209$ | $90$ |
| F29 $(2,3,5)$ | $30$ | $21$ | $8$ | $0$ | $110$ | $21/8$ | $55/8$ | $4/55$ | $72$ |
| F30 $(2,3,7)$ | $42$ | $33$ | $12$ | $0$ | $170$ | $11/4$ | $85/12$ | $6/85$ | $96$ |
| F31 $(2,5,7)$ | $70$ | $77$ | $24$ | $0$ | $374$ | $77/24$ | $187/24$ | $12/187$ | $144$ |
| F32 $(2,5,9)$ | $90$ | $105$ | $32$ | $0$ | $506$ | $105/32$ | $253/32$ | $16/253$ | $180$ |
| F33 $(2,7,9)$ | $126$ | $165$ | $48$ | $0$ | $782$ | $55/16$ | $391/48$ | $24/391$ | $240$ |
| F34 $(3,4,5)$ | $60$ | $105$ | $24$ | $6$ | $440$ | $33/8$ | $217/24$ | $12/217$ | $120$ |
| F35 $(3,4,7)$ | $84$ | $165$ | $36$ | $10$ | $680$ | $155/36$ | $335/36$ | $18/335$ | $160$ |
| F36 $(3,5,7)$ | $105$ | $231$ | $48$ | $15$ | $935$ | $9/2$ | $115/12$ | $6/115$ | $192$ |
| F37 $(3,5,8)$ | $120$ | $273$ | $56$ | $18$ | $1100$ | $255/56$ | $541/56$ | $28/541$ | $216$ |
| F38 $(3,7,8)$ | $168$ | $429$ | $84$ | $30$ | $1700$ | $19/4$ | $835/84$ | $42/835$ | $288$ |
| F39 $(4,5,7)$ | $140$ | $385$ | $72$ | $30$ | $1496$ | $355/72$ | $733/72$ | $36/733$ | $240$ |
| F40 $(4,5,9)$ | $180$ | $525$ | $96$ | $42$ | $2024$ | $161/32$ | $991/96$ | $48/991$ | $300$ |
| F41 $(4,7,9)$ | $252$ | $825$ | $144$ | $70$ | $3128$ | $755/144$ | $1529/144$ | $72/1529$ | $400$ |
| F42 $(5,6,7)$ | $210$ | $693$ | $120$ | $60$ | $2618$ | $211/40$ | $1279/120$ | $60/1279$ | $336$ |
| F43 $(5,7,8)$ | $280$ | $1001$ | $168$ | $90$ | $3740$ | $911/168$ | $1825/168$ | $84/1825$ | $432$ |
| F44 $(5,7,9)$ | $315$ | $1155$ | $192$ | $105$ | $4301$ | $175/32$ | $1049/96$ | $48/1049$ | $480$ |
| F45 $(5,8,9)$ | $360$ | $1365$ | $224$ | $126$ | $5060$ | $177/32$ | $2467/224$ | $112/2467$ | $540$ |
| F46 $(7,8,9)$ | $504$ | $2145$ | $336$ | $210$ | $7820$ | $645/112$ | $3805/336$ | $168/3805$ | $720$ |
| F47 $(2,3,5,7)$ | $210$ | $231$ | $48$ | $0$ | $1870$ | $77/16$ | $935/48$ | $24/935$ | $576$ |

以下边界表改用未除以 $t$ 的整数向量 $\nu$；实际等基数集合各有 $(P-h)/2$ 个点。空族只有零向量，不能将它归一化成概率来源。

| 模数族 | $C_0$ | $\lVert F\nu\rVert_{\rm obs}$ | 规范半径 | 每份实际集合基数 |
| --- | --- | --- | --- | --- |
| 边界 $()$ | $0$ | $0$ | 不定义 | $0$ |
| 边界 $(2)$ | $1$ | $1$ | $1/2$ | $1$ |
| 边界 $(3)$ | $1$ | $2$ | $1/2$ | $2$ |
| 边界 $(2,3)$ | $3/2$ | $2$ | $1/5$ | $5$ |
| 边界 $(3,5)$ | $9/4$ | $8$ | $2/13$ | $26$ |


#### 8.9.5 概率输出的共同中心与来源族

设 $m\ge2$，$K\subseteq\Delta_m$ 是非空紧来源集，例如单纯形与逐格闭区间的非空交集。给定其格极值 $l_i,u_i$，概率中心半径 $s$ 可行，当且仅当每个区间 $[\max(0,u_i-s),l_i+s]$ 非空，且下界和不超过一、上界和不少于一。这个等价关系由第 8.7.2 节的固定顺序填充法证明；它给出独立于 ER8.SO.1 的精确半径
$$
\max\left\{0,\max_i\frac{u_i-l_i}{2},
\frac{1-\sum_i l_i}{m},
\max_{\varnothing\ne S\subseteq[m]}\frac{\sum_{i\in S}u_i-1}{|S|}\right\}.
$$
其中各区间非空给第二项，上界和条件给第三项；下界和条件等价于对全部 $S$ 有 $\sum_{i\in S}(u_i-s)\le1$，给第四项。最后一项可按子集基数依次选最大的 $u_i$ 求得。实向量输出中心半径则为 $\max_i(u_i-l_i)/2$。

对任意单模数拟合向量 $a_i=1-\widehat y_i$ 和 $\varepsilon\ge0$，取 $L_i=\max(0,a_i-\varepsilon)$、$U_i=\min(1,a_i+\varepsilon)$。在空读数满足其合法噪声界的前提下，可能来源集 $\Delta_m\cap\prod_i[L_i,U_i]$ 非空，当且仅当 $L_i\le U_i$ 对每格成立且 $\sum_iL_i\le1\le\sum_iU_i$；其精确格极值由第 8.7.3 节给出。若还要求观测本身是某个概率来源的精确响应，则另须 $a\in\Delta_m$ 且空读数为一。有限来源集也可直接使用其坐标极值求上述共同中心，无需改变半径公式。

提升轨道对偶时，非目标删除标签先均匀平均；该平均读数在目标格的保留概率是一，在其他格是 $(m_i-2)/(m_i-1)$。它仍是原始带标签读数的凸组合，再逐个原坐标核对对偶恒等式，不能将一个轨道系数当成任意固定非目标余数的系数。

在任一非空可行纤维上，已知可行中心半径 $s$ 后，令 $A_i=\max(0,u_i-s)$、$B_i=l_i+s$，固定坐标顺序并定义
$$
r_0=1-\sum_i A_i,\qquad
z_i=\min(B_i-A_i,r_{i-1}),\qquad
q_i=A_i+z_i,\qquad r_i=r_{i-1}-z_i.
\tag{ER8.CENTER.1}
$$
由 $\sum A_i\le1\le\sum B_i$ 和 $A_i\le B_i$，归纳有 $r_i\ge0$，且 $r_m=0$；否则所有容量都已填满而总容量仍小于 $r_0$，矛盾。因此 $q\in\Delta_m$，并同时满足每个坐标的全部来源约束。该递推也明确规定一个确定性中心。若输入纤维为空，则按第 8.7.3 节输出预先固定的概率律。



##### 8.9.5.1 四十九个任意噪声的共同输入来源族

参数为 $m=2,\ldots,8$ 及 $\varepsilon\in\{0,1/10,1/4,1/2,3/4,1,2\}$。对 $\varepsilon\le1/2$，每族使用第 8.7.4 节的全部 $p^{(j)}=b+2\varepsilon e_j$ 与唯一共同观测 $\widehat y=1-b-\varepsilon$；对更大半径使用全部顶点及 $\widehat y_i=1/2$。表中 $s=\sum_i(1-\widehat y_i)$ 是该共同输入的拟合质量，不是任意真实来源的质量（真实来源始终归一）。两种输出风险由第 8.7 节的匹配上下界证明。

| 族／$m$ | $\varepsilon$ | 概率输出风险 | 实输出风险 | 共同输入的拟合质量 $s$ |
| --- | --- | --- | --- | --- |
| N01 $2$ | $0$ | $0$ | $0$ | $1$ |
| N02 $2$ | $1/10$ | $1/10$ | $1/10$ | $1$ |
| N03 $2$ | $1/4$ | $1/4$ | $1/4$ | $1$ |
| N04 $2$ | $1/2$ | $1/2$ | $1/2$ | $1$ |
| N05 $2$ | $3/4$ | $1/2$ | $1/2$ | $1$ |
| N06 $2$ | $1$ | $1/2$ | $1/2$ | $1$ |
| N07 $2$ | $2$ | $1/2$ | $1/2$ | $1$ |
| N08 $3$ | $0$ | $0$ | $0$ | $1$ |
| N09 $3$ | $1/10$ | $2/15$ | $1/10$ | $11/10$ |
| N10 $3$ | $1/4$ | $1/3$ | $1/4$ | $5/4$ |
| N11 $3$ | $1/2$ | $2/3$ | $1/2$ | $3/2$ |
| N12 $3$ | $3/4$ | $2/3$ | $1/2$ | $3/2$ |
| N13 $3$ | $1$ | $2/3$ | $1/2$ | $3/2$ |
| N14 $3$ | $2$ | $2/3$ | $1/2$ | $3/2$ |
| N15 $4$ | $0$ | $0$ | $0$ | $1$ |
| N16 $4$ | $1/10$ | $3/20$ | $1/10$ | $6/5$ |
| N17 $4$ | $1/4$ | $3/8$ | $1/4$ | $3/2$ |
| N18 $4$ | $1/2$ | $3/4$ | $1/2$ | $2$ |
| N19 $4$ | $3/4$ | $3/4$ | $1/2$ | $2$ |
| N20 $4$ | $1$ | $3/4$ | $1/2$ | $2$ |
| N21 $4$ | $2$ | $3/4$ | $1/2$ | $2$ |
| N22 $5$ | $0$ | $0$ | $0$ | $1$ |
| N23 $5$ | $1/10$ | $4/25$ | $1/10$ | $13/10$ |
| N24 $5$ | $1/4$ | $2/5$ | $1/4$ | $7/4$ |
| N25 $5$ | $1/2$ | $4/5$ | $1/2$ | $5/2$ |
| N26 $5$ | $3/4$ | $4/5$ | $1/2$ | $5/2$ |
| N27 $5$ | $1$ | $4/5$ | $1/2$ | $5/2$ |
| N28 $5$ | $2$ | $4/5$ | $1/2$ | $5/2$ |
| N29 $6$ | $0$ | $0$ | $0$ | $1$ |
| N30 $6$ | $1/10$ | $1/6$ | $1/10$ | $7/5$ |
| N31 $6$ | $1/4$ | $5/12$ | $1/4$ | $2$ |
| N32 $6$ | $1/2$ | $5/6$ | $1/2$ | $3$ |
| N33 $6$ | $3/4$ | $5/6$ | $1/2$ | $3$ |
| N34 $6$ | $1$ | $5/6$ | $1/2$ | $3$ |
| N35 $6$ | $2$ | $5/6$ | $1/2$ | $3$ |
| N36 $7$ | $0$ | $0$ | $0$ | $1$ |
| N37 $7$ | $1/10$ | $6/35$ | $1/10$ | $3/2$ |
| N38 $7$ | $1/4$ | $3/7$ | $1/4$ | $9/4$ |
| N39 $7$ | $1/2$ | $6/7$ | $1/2$ | $7/2$ |
| N40 $7$ | $3/4$ | $6/7$ | $1/2$ | $7/2$ |
| N41 $7$ | $1$ | $6/7$ | $1/2$ | $7/2$ |
| N42 $7$ | $2$ | $6/7$ | $1/2$ | $7/2$ |
| N43 $8$ | $0$ | $0$ | $0$ | $1$ |
| N44 $8$ | $1/10$ | $7/40$ | $1/10$ | $8/5$ |
| N45 $8$ | $1/4$ | $7/16$ | $1/4$ | $5/2$ |
| N46 $8$ | $1/2$ | $7/8$ | $1/2$ | $4$ |
| N47 $8$ | $3/4$ | $7/8$ | $1/2$ | $4$ |
| N48 $8$ | $1$ | $7/8$ | $1/2$ | $4$ |
| N49 $8$ | $2$ | $7/8$ | $1/2$ | $4$ |


#### 8.9.6 自洽观测全尺度的连续纤维族

取 $m=2,\ldots,6$，令 $A_m=\{a\in\Delta_m:6a_i\in\mathbb N\ \forall i\}\cup\{u_m\}$，其中 $u_m=(1/m,\ldots,1/m)$，重复点只计一次；令 $E_m=\{0,1/12,1/4,1/2,2/3,3/4,1-1/m,1,2\}$，重复半径只计一次。这给 $42$ 组维数／半径及按 $(m,a,\varepsilon)$ 索引的 $7017$ 个完整连续纤维 $K(a,\varepsilon)=\Delta_m\cap\prod_i[a_i-\varepsilon,a_i+\varepsilon]$。每个纤维包含其区间约束下的全部实概率来源；不同索引允许对应同一来源集合。第 8.9.5 节给每个纤维的精确中心半径；ER8.CS.1 给共同上界。每组的概率输出最大半径在 $a=u_m$ 达到，实输出最大半径在 $a=(1/2,1/2,0,\ldots,0)$ 达到；这两个 $a$ 都在 $A_m$ 中，不要求同一个 $a$ 同时最坏。

每个 $A_m$ 的网格部分有 $\binom{m+5}{m-1}$ 个元素；只有 $m\nmid6$ 时均匀点才是额外元素。各域大小为：

| 维数与连续纤维族 | $\lvert A_m\rvert$ | $\lvert E_m\rvert$ | $\lvert A_m\times E_m\rvert$ | 概率下界来源的索引数 $m\lvert E_m\rvert$ | 实下界来源的索引数 $2\lvert E_m\rvert$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $m=2$ 的自洽域 | 7 | 8 | 56 | 16 | 16 |
| $m=3$ 的自洽域 | 28 | 8 | 224 | 24 | 16 |
| $m=4$ 的自洽域 | 85 | 8 | 680 | 32 | 16 |
| $m=5$ 的自洽域 | 211 | 9 | 1899 | 45 | 18 |
| $m=6$ 的自洽域 | 462 | 9 | 4158 | 54 | 18 |

网格点与非负整数解 $k_1+\cdots+k_m=6$ 一一对应：把六颗星与 $m-1$ 个隔板排成一行，第 $i$ 段的星数为 $k_i$，故从 $m+5$ 个位置选择隔板给 $\binom{m+5}{m-1}$ 种。均匀点在网格内当且仅当 $m\mid6$。前三个维数的 $1-1/m$ 已在固定半径列表中，后两个维数各多一个半径；对 $m$ 求和，$\sum_m|E_m|=42$、$\sum_m|A_m||E_m|=7017$，其余两列给下界来源的索引数。每个纤维的来源集合仍为连续集合，并不只有这些网格点。

在这 $42$ 个参数组中，ER8.CS.2 各给按 $j=1,\ldots,m$ 索引的共同输入概率输出下界来源，共 $171$ 项；每组的实输出成对构造共给 $84$ 项。合计 $255$ 项按参数及来源标签计数，允许概率向量重复，例如零半径时同组来源重合。对每项来源及其共同观测来源，同时作任意有理 $0<\delta<1$ 的均匀混合，便得到严格正的版本，分离量乘以 $1-\delta$。归一化、合法噪声及分离关系由第 8.8.2 节的直接证明成立。

### 8.10. 成熟接口与结论边界

#### 8.10.1 共同来源、历史可达性与既有任务接口

理论背景采用固定版本定位。提交 `625f417c1fbab0084ceab6dd7de75ebddca84532` 的《有效分辨率》§1.1.1–1.1.5、TM.352–364，声明同一实际集合的提升、删除、密度、首次删空层及共同轮廓。ER8.FH.21 是 TM.355 在 $m=tL$ 时的特化，ER8.FH.10 与不增大分辨率的 $k=1$ 删除支路相容。同版本《运输、记忆与完成化》的完整历史摘要最小性以全部合法续接、确定性更新和无隐藏旁路为条件，并只对可达像计数；ER8.FH.11–ER8.FH.14 保留这些界限。其具体群运输另有可逆执行等前提，不能把那份具体实现的可达轨道结论直接套到任意同余历史。

《上下文时空算术与机器学习》相关任务接口分别要求目标、动作合法性、后继与费用下降。本文布尔商只压缩所声明的布尔目标，未声称同时保留实际成本或完整档案。合法控制信息可以保存在内部状态，也可以由外部控制器提供；后者不应重复计作内部记忆，但不能在数学接口中消失。

以下项目接口以固定提交 `4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c` 为来源坐标，其一般结论与本文具体识别分别承担不同义务：

| 既有接口 | 与本题的精确关系和限制 |
|---|---|
| [D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean)，`target_family_minimal_quotient` | 给任意目标族共同核的最小商、目标下降及所有充分读出的核包含；本题目标分别取全部合法精确计数或布尔读数。它不自行识别直方图、七类或噪声锐常数。 |
| [D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.lean)，`joint_residue_image_eq_compatible_pairs` | 共同余数像由 gcd 相容性精确刻画，使用 `Nat.chineseRemainder'`；ER8.FH.10 按实际共同像求交，不能把两边缘自由组合。 |
| [D5/S3/Observer/Separation/FiniteFutureCongruence.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/Separation/FiniteFutureCongruence.lean)，`finite_future_maximal_congruence`；[D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.lean)，`minimal_predictive_completion_quotient` | 给有限未来合同及预测商，但原接口针对一个更新；本文由剩余 $M$ 控制多动作，须另核对其动作域对应。 |
| [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)，`controlledBehavior`、`completionUpdate`、`controlled_behavior_universal_property` | 给所有有限控制词的行为商、更新，以及满足交换关系的有限实现到最小商的唯一满射和基数界。更新为全定义时，必须将剩余 $M$ 加入状态，并为非法重复动作指定失败状态／输出；也可经部分任务合同适配，不能直接忽略非法动作。 |
| [D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)，`dynamic_closure_is_least` | 给一般最小动态稳定细化；它不计算本题具体证书反链和七种规范形。 |
| [D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality.lean)，`source_cutset_hitting_duality` | 有限单调语义的切断与最小支持击中对偶。以可用动作源集合 $A$ 上的可证明性为“存在实际 $r\in S$ 使 $E_r\subseteq A$”，得到删空／击中骨架；本题还要求每模数至多一标签，不能用无约束最小击中数代替合法最小值。 |
| [D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality.lean) | 提供规范包含极小支持版本；与一般对偶同属已有结构，不代替本题动作约束的核对。 |

两份二元几何接口还提供共同相位和切片的具体背景：[D5/S3/Arith/Covering/BinaryAffineGeometry.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Arith/Covering/BinaryAffineGeometry.lean) 的 `mixed_cover_iff` 对 $\mathbb F_2^2$ 上的满集、三方向直线和单点给覆盖的六类判据及27种互异最小形状；[D5/S3/Arith/Covering/MixedAffineQuotient.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Arith/Covering/MixedAffineQuotient.lean) 的 `result` 在逐行周期正且整除 $2M_0$ 时，保留 guard、逐行合取和原相位，将两个整数坐标在同一基点的四个提升表示为空／满／线／点切片，并给精确见证及覆盖等价。这里以 $M_0$ 区别该接口中的标量与本文模数集合 $M$。

这两份二元四提升模型没有声明任意模 $L$ 的完整未来计数、动态直方图或商类数。本文也未给任意一维状态到它们的归约映射，不能把其结论当成 定理 8.1 的直接证明。有限包含排除／Möbius 反演、CRT、击中集与目标族取商是标准组成结构；具体数学内容由前文显示的反演、更新和分类证明承担。

#### 8.10.2 数值稳定性不能由其他范数或来源合同替代

矩阵工具采用钉版 Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` 的 `Matrix.linfty_opNorm_def`、`Matrix.linfty_opNorm_mulVec` 和 `Matrix.mul_kronecker_mul`，分别对应行绝对和、矩阵作用上界及张量乘法。本文还须独立供应共同锐见证、非负基线、零和修正和指定输出域下的共同中心；这些义务不由算子可逆性单独完成。

相关结果的合同不能混用：

| 相邻接口 | 不能直接替换本题的原因 |
|---|---|
| [TargetVisibilityConditionCost.target_visibility_condition_cost](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/Conditioning/TargetVisibilityConditionCost.lean) | 使用内积、正规方程及 Hilbert 范数系数代价，未给本文逐坐标最大范数常数。 |
| [RobustFrameBounds.robust_observer_frame_bounds](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/Linear/RobustFrameBounds.lean)；[DualGramConditionNumber.dual_gram_condition_number](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/LinearMemory/DualGramConditionNumber.lean) | 处理 Gram 谱、Euclidean 或奇异值条件数，范数与常数不同。 |
| [RobustMinimaxKernelBound.common_kernel_minimax_lower_bounds](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.lean)；[TestingDivergenceBounds](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Estimation/TestingDivergenceBounds.lean) | 处理同核转录下的二分类零一损失、Bayes 或概率检验风险，不直接给直方图最大坐标损失的有界加性噪声公式。 |
| [NonconvexSharpIdentification.exact_lower_endpoint_of_valid_bound_and_witness](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.lean) | 整理有效界和达到见证的一般关系；本题的有效界及共同见证仍须具体构造。 |
| [NoisyMomentAtomExtremum.finite_noisy_exterior_atom_sharp](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Analytic/NoisyMomentAtomExtremum.lean) | 来源归一化且采用受限小噪声，但观察是原始矩、目标是外部原子；不是同余删除算子。 |
| [Conditioning.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/Conditioning.lean)、[ConditioningCertificate.lean](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Observer/ConditioningCertificate.lean) | 量子条件化及其缺陷，与这里的数值稳定性常数不是同一问题。 |
| [FarkasAlternative.equality_farkas](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Analytic/Convexity/FarkasAlternative.lean)、`inequality_farkas` | 提供一般线性对偶基础；不能省去本文原始可行见证与精确对偶恒等式。 |
| [FractionalKnapsackDual.fractional_knapsack_strong_duality](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/D5/S3/Analytic/Knapsack/FractionalKnapsackDual.lean) | 对应另一类单预算可行域，不是给定总质量下全部删除读数的联合约束。 |

“固定总质量”也不同于“固定某个点的质量”。本文的约束是所有坐标之和已知；概率来源两两之差落在零和子空间，而估计器输出是否仍须属于概率单纯形是额外条件。源范数常数 $C_0$ 不自动决定每种受约束输出的 minimax 风险，ER8.SO.1 已给出明确反例。

#### 8.10.3 保留的范围与待解决关系

本文的全域精确计数类数和布尔类数，对任意初始集合成立；对历史可达域，只能计算该域在相应直方图或反链下的实际像。严格全奇、模数互异且大于一的可达前缀若被合法全奇续接删空，就已经构成同一整数覆盖。两组含偶数准备的实际反例，以及奇周期中的张量见证，均没有履行这项更强可达义务。

同一响应等价类的最大支持是行为规范表示，不能被当成新增实际点或可达历史证书。重新允许已消费模数、开放新模数、加入点身份、精确计数、来源档案或费用，都可能改变原来的任务商。固定单余数测试的分离判据也仅对“一模数一个预定余数”的协议有效。

自由质量锐常数 $\kappa$、固定总质量零和常数 $C_0$、实向量输出的局部 minimax，以及自洽观测的概率输出局部 minimax，分别具有已展示的匹配上下界。ER8.SO.1 与 ER8.CS.1 又给出单模数、两种观测合同、两种输出域的全部噪声尺度。一般多模数组合的全尺度 minimax，尤其任意逐格有界噪声下的概率输出风险，以及自洽观测超出 ER8.CM.7 所给充分半径后的风险，未由本文求出；该半径也未被证明最大。

固定周期的每格容量、整数性、历史可达性和严格正坐标的统一下界会改变来源域。本章给出的算术操作和 oracle 查询上界不确定样本复杂度、最优 oracle 查询数或最优位复杂度。

#### 8.10.4 参数对应与直接使用的范围

固定 $(L,M)$ 时，在 `target_family_minimal_quotient` 中取状态域 $X=\mathcal P(X_L)$，或明确指定的实际来源子域；指标 $I$ 是全部合法带标签部分查询，目标值域分别为 $\mathbb N$ 与布尔值，目标函数分别为 $R_{T,a}$ 与 $b_C$。任意充分摘要的值域取它的实际像 $O$；ER8.FH.7 与 ER8.FB.9 分别识别目标共同核为直方图核与反链核。于是一般核包含给最小因子，而具体反演和分类仍由第 8.1、8.3 节证明。若摘要还依赖历史，则应先把该历史纳入来源域，不能假定它已经是 $H$ 的函数。

对《上下文时空算术与机器学习》定理 2.2、3.2 的部分动作接口，状态取 $(M,H)$，动作 $e=(m,a)$ 的定义域是 $m\in M$，后继为 $(M\setminus\{m\},H\setminus(a\bmod m))$，摘要为 $(M,N_D)$ 或 $(M,\mathcal K_M)$。保留 $M$ 使合法域在摘要纤维上饱和；ER8.FH.8 或 ER8.FB.10 给后继下降。输出只取所声明的计数或布尔读数。若任务包含费用，可取明确的仅依赖合法标签的费用，或另外证明实际费用在纤维上恒定；本章没有把任意档案和费用自动压入这些商。

若采用 `controlled_behavior_universal_property` 的全动作接口，先固定初始 $M_0$。其有限状态载体取全部 $M\subseteq M_0,H\subseteq X_L$，再加吸收失败态；控制字母为全部初始模数的余数标签。合法动作按上段执行，非法或重复动作进入失败态。读出区分失败，并在其他状态保留 $M$ 与指定当前读数。实现载体 $W$ 取上述摘要的实际像及失败态；这样 $Y\to W$ 满射，读出和更新的交换关系由已证公式成立。受限历史域还须对合法后继封闭。该普适性质的状态空间包含变化的控制域；固定 $M$ 的类数只计其中一个控制域的状态商。`dynamic_closure_is_least` 可取同一载体，保留原接口 `Refines(coarse,fine)` 的方向；单更新的 `FiniteFutureCongruence` 与 `MinimalPredictiveCompletionQuotient` 不直接充当这个多动作实例。

对两份来源切断／击中对偶，取有限 `Source` 为 $\mathcal A_M$，定义 $\operatorname{provable}(A)\iff\exists r\in S:E_r\subseteq A$。这个谓词单调。移除 $C$ 后不存在这样的证明，当且仅当 $C$ 击中每个 $E_r$。所有不同的 $E_r$ 基数相同，故它们恰给存在支持的包含极小元；空支持和空边另按定义处理。随后才限制 $C$ 每模数至多一个标签。原接口的无约束最小击中基数不替代此合法最小值。

在 `joint_residue_image_eq_compatible_pairs` 与 `Nat.chineseRemainder'` 中，ER8.FH.10 的参数是正模数 $d,m\mid L$ 和余数 $b,a$。相容前提为模 $\gcd(d,m)$ 相等；`Nat.chineseRemainder'_lt_lcm` 给模 LCM 内的代表，`Nat.mod_lcm` 给相容类唯一性，且 $\operatorname{lcm}(d,m)\mid L$。这一共同像仍须由实际 $H$ 供应格内数量。两两互素时才逐次取得第 8.5–8.6 节所用的整个 CRT 乘积；它不是来源边缘独立的断言。

矩阵恒等式的参数为实标量、CRT 乘积的有限行列指标及 $B=\bigotimes_i(J/(m_i-1)-I)$。矩阵范数取无穷算子范数，向量范数取最大坐标范数，对应于 `Matrix.Norms.Operator` 的 `linfty_opNorm_def`、`linfty_opNorm_mulVec` 及 `linfty_opNorm_eq_opNorm`。恒等式 $J^2=m_iJ$ 给每个因子互逆；`mul_kronecker_mul`、`one_kronecker_one` 与乘积重编号给张量逆式，包括空张量边界。行绝对和、共同锐见证、零和移心及非负基线由第 8.5–8.6 节给出；这些常数以所指定的范数为条件。

有理 LP 若通过 `equality_farkas` 或 `inequality_farkas` 表述，可将自由变量写成两个非负变量之差，对每条响应加入正负两侧单位上界，并保留或精确消去零和等式。ER8.LP.1 已直接给弱对偶与达到见证，不依赖另一个未展开的求解结论。所有非目标删除系数须先按原始标签平均后再提升。

本卷已有 TM.355 的固定分辨率支路取 $m\mid L$、提升因子为一；ER8.FH.21 取 $m=tL$、$d=L$、提升因子为 $t$，旧 $R_L(a)$ 正是成员示性位。已有 TM.359 保留严格提升不能首次删空的边界。历史摘要最小性的复用限于全部合法续接、确定性更新、实际可达像与无隐藏旁路；可逆群轨道模型还需可执行逆路径，不能对不可逆同余删除直接援引。


直接上游矩阵和同余来源为钉版 Mathlib 的 [Normed](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Matrix/Normed.lean)、[Kronecker](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Kronecker.lean) 与 [ModEq](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Nat/ModEq.lean)。历史接口定位为 [有效分辨率 §§1.1.1–1.1.5](https://github.com/the-omega-institute/trureturing/blob/625f417c1fbab0084ceab6dd7de75ebddca84532/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md)、[运输、记忆与完成化 §2.1](https://github.com/the-omega-institute/trureturing/blob/625f417c1fbab0084ceab6dd7de75ebddca84532/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) 及 [上下文时空算术与机器学习 §§2–3](https://github.com/the-omega-institute/trureturing/blob/625f417c1fbab0084ceab6dd7de75ebddca84532/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)。

## 追加锚（本行以下为增补区）
