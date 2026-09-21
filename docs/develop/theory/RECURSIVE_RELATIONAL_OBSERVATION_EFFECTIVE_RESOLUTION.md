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

profile343 的A卷第3.5节已经区分“最终高度表可判定”和“禁类仅以事件流给出”，并提醒冗余禁类的原始清单不能从幸存集合中自动恢复。上述反例把这种信息区别具体落在规范基的可枚举性上，不改变该节既有结算。

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
