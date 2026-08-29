# 治理不动点理论
## Governance Fixed-Point Theory（GFPT）

> **状态**：理论纲领与可形式化内核，v1.0，2026-08-29。  
> **写入纪律**：本卷是独立于 DECT 的姊妹卷；不修改、不替换、不重新编号 DECT 的任何段落。后续修订只追加于本卷末尾。  
> **对象边界**：DECT 研究定义如何追上概念；GFPT 研究治理校验器如何判定自身账本状态，以及校验规则如何在不改写旧真的条件下获得新的合法修复通道。  
> **证明状态**：本卷冻结 G-A—G-H 八条精确证明义务。它们在进入 Lean 内核并无 `sorry` 证毕之前均为 `open`，本文不把定理骨架冒充已证定理。  
> **主张边界**：本文不证明任意状态派生器的业务语义正确，不证明密码学哈希的全局无碰撞，不证明文件系统原子性或并发活性，也不把任意文本前缀扩展冒充语义等价。

---

## 摘要

一个治理门通常执行极简单的检查：条目的手写状态是否等于机器从其余事实派生出的状态。困难不在这个等号，而在等号两侧是否真正独立。

若派生函数读取它正在校验的当前手写状态，则门方程成为自指方程。此时即使派生器在每个分支上都“有理由”，系统也可能没有任何可接受状态。两状态翻转是最小非退化反例：条目写成 `partial` 时派生器要求 `absorbed`，写成 `absorbed` 时又要求 `partial`。

若派生函数对当前手写状态结构性盲，即完整派生流水线可因子化为只读取状态以外上下文的函数，则门方程恒有且仅有一个解：把手写状态写成派生值本身。

另一类故障来自追加式载体。内容寻址条目引用卷尾 span 时，向卷尾追加内容必然改变该 span 的字节和内容键。旧字节不可改、基线字节不可删、孤儿对象不可造，这些规则各自合理；但它们的合取可能使整个修复类不可达。正确做法不是放宽旧规则，而是增加一个有名、类型化、仅覆盖该死锁类的重键通道。

GFPT 的三条中心纪律是：

1. **当前状态是派生输出坐标，不得成为自身派生输入坐标。**
2. **地址漂移是表示事件，不是旧真值的重新裁决事件。**
3. **规则合取封死合法修复时，增加窄通道，不改写旧规则的放行集。**

---

# 第一部　对象与动机

## 1.1 治理系统

固定：

- 条目类型 $E$；
- 状态类型 $\Sigma$；
- 状态以外的治理上下文类型 $C$；
- 当前手写状态 $h:E\to\Sigma$；
- 完整状态派生流水线 $D:C\to(E\to\Sigma)\to(E\to\Sigma)$。

这里的“完整流水线”包括加载、规范化、依赖收集、coverage 计算、收据解释、路径解码和最终状态归约。不能只证明最后一个局部函数不读取状态，却允许前置 loader 从状态目录、状态字段或状态编码路径中把同一信息重新送入。

定义等号门：

$\operatorname{Gate}(h,d)\Longleftrightarrow\forall e:E,\ h(e)=d(e)$。

一般自读系统在上下文 $c:C$ 上的通过条件为：

$\operatorname{Pass}_D(c,h)\Longleftrightarrow\operatorname{Gate}(h,D(c,h))$。

一个 GFPT 治理系统记为：

$\mathfrak G=(E,\Sigma,C,h,D,\operatorname{Gate})$。

门只判一致性，不负责创造事实。派生函数负责从规范输入给出候选状态；手写状态是待核对的表示；门负责确认二者相同。

若具体系统使用自定义门 $G$，则必须证明它与上述逐条等号门外延等价。仅仅“在当前夹具上给出相同布尔值”不足以成为第二个门定义。

## 1.2 当前状态与其余输入的分割

应用 GFPT 前，原始快照必须被规范分解为：

$\operatorname{Raw}\longrightarrow(C,h)$。

其中 $C$ 在只改变当前手写状态时保持不变。下列对象都属于当前状态的别名，不能偷偷留在 $C$ 中：

- YAML 或 TOML 中的当前 `status` 字段；
- 表示 `partial`、`absorbed` 等状态的目录位置；
- 由当前状态决定的文件名、bucket、活动队列或索引；
- 能无损恢复当前状态的序列化副本；
- 先读取当前状态、再以另一名称输出的“派生前件”。

允许进入 $C$ 的是与当前候选状态严格分离的事实，例如内容字节、冻结收据、coverage 边、声明版本、规范依赖闭包和严格更早版本的冻结状态。

若需要读取上一版本状态，应使用守卫形式：

$h_{n+1}=d(c_n,h_n^{\mathrm{frozen}})$，

而不是：

$h_{n+1}=D(c_n,h_{n+1})$。

前者引用已完成旧层；后者在同一层读回待判输出。

## 1.3 实案一的抽象：单变量状态翻转

取一个条目和两个状态：

$\Sigma=\{\mathsf{partial},\mathsf{absorbed}\}$。

定义自读派生器：

$F(\mathsf{partial})=\mathsf{absorbed}$，且  
$F(\mathsf{absorbed})=\mathsf{partial}$。

门方程是 $s=F(s)$。穷举矩阵为：

| 手写状态 $s$ | 派生状态 $F(s)$ | 门结果 |
|---|---|---|
| $\mathsf{partial}$ | $\mathsf{absorbed}$ | 拒绝 |
| $\mathsf{absorbed}$ | $\mathsf{partial}$ | 拒绝 |

故不存在通过状态。

这不是“操作者选错了目录”，也不是“再跑一次即可收敛”。它是函数本身无不动点。只要派生器继续读取当前状态，任意次数的目录往返都不会产生解。

## 1.4 实案二的抽象：尾节漂移与双律死锁

设源卷字节串为 $x$，卷尾追加字节为 $u$，新卷为 $y=x\cdot u$。某内容寻址条目引用从偏移 $m$ 到卷尾的 span。追加前后的 span 字节分别为：

$\operatorname{Tail}(x,m)$ 与 $\operatorname{Tail}(y,m)$。

即使旧字节一字未改，只要 $u$ 非空，尾节内容键就会变化。

此时两条局部规则可能同时生效：

- 规则 A：不得留下无规范引用的孤儿内容对象；
- 规则 B：不得删除已经进入基线的内容对象。

若旧操作字母表只提供“保留”或“删除”，则：

- 保留陈旧对象可能触发 A；
- 删除陈旧对象可能触发 B；
- 两条规则的合取没有合法动作。

这不是 A 或 B 单独错误，而是合法修复类没有被现有操作语言表达。需要增加的不是全局豁免，而是第三种动作：保留旧历史、退役陈旧引用边、为新 span 生成新键，并把活动索引迁移到新键。

## 1.5 本卷的证明范围

GFPT v1.0 只承诺以下数学内核：

- 状态盲派生器的门方程有唯一解；
- 两元素翻转给出无不动点反例；
- 卷尾 span 在前缀追加下仍为前缀扩展；
- 合法尾节重键结果存在、唯一且保守；
- 修复死锁等价于修复类与联合放行集交为空；
- 对死锁类存在只增加该类的新通道。

以下问题不由这些定理自动解决：

- 派生值是否符合业务规范；
- 哪些逻辑 ID 有资格使用尾节重键；
- 哈希算法在无限字节域上是否无碰撞；
- 并发写入和崩溃恢复是否线性化；
- 新增文本是否包含必须另行裁决的新命题；
- 某条本地拒绝规则是否值得保留。

这些必须由实现层、来源账和另外的证明义务承担。

---

# 第二部　派生盲性与不动点

## 2.1 结构性盲派生器

定义盲派生器：

$d:C\to(E\to\Sigma)$。

其类型中没有当前手写状态实参。把它提升到一般自读接口：

$\operatorname{liftBlind}(d)(c,h):=d(c)$。

定义一般派生器 $D$ 对当前手写状态盲，当且仅当存在一个盲派生器 $d$，使：

$\forall c:C,\ \forall h:E\to\Sigma,\quad D(c,h)=d(c)$。

等价地，$D$ 通过投影 $(c,h)\mapsto c$ 因子化。

本定义要求的是完整派生流水线的因子化。若 loader 读取状态目录并把它改名为 `locationClass`，最终归约器即使不再读取名为 `status` 的字段，完整流水线仍不盲。

规范实现应直接暴露 $d:C\to(E\to\Sigma)$。因子化谓词只用于审计和迁移旧接口，不应成为长期保留自读签名的理由。

## 2.2 盲派生唯一不动点定理骨架

若 $D$ 状态盲，则对每个固定上下文 $c$，存在唯一手写状态函数 $h$ 通过门：

$\operatorname{StatusBlind}(D)\Longrightarrow\forall c:C,\ \exists!h:E\to\Sigma,\ \operatorname{Gate}(h,D(c,h))$。

证明骨架如下：

1. 由盲性取得 $d$，满足 $D(c,h)=d(c)$；
2. 取见证 $h_0:=d(c)$；
3. 逐条有 $h_0(e)=D(c,h_0)(e)$；
4. 若 $h_1$ 也通过，则逐条有 $h_1(e)=d(c)(e)$；
5. 函数外延给出 $h_1=h_0$。

该结果不要求：

- $E$ 有限或非空；
- $\Sigma$ 有可判等号；
- $\Sigma$ 有序；
- 存在迭代收敛过程；
- 有度量、概率、测度或拓扑结构。

它证明的是门方程良定，不是 $d$ 的业务正确性。一个完全盲但错误的派生器仍有唯一一致状态；其错误必须由独立语义规范发现。

## 2.3 非盲派生没有统一保证

状态不盲并不逻辑蕴含“必无不动点”。非盲函数可能有零个、一个或多个不动点。GFPT 的结论是：

- 盲性给出对所有上下文的统一存在唯一保证；
- 放弃盲性后，该统一保证失效；
- 两元素翻转给出最小非退化失败见证。

取 `Bool`，定义：

$\operatorname{flip}(\mathsf{false})=\mathsf{true}$，  
$\operatorname{flip}(\mathsf{true})=\mathsf{false}$。

则：

$\neg\exists s:\operatorname{Bool},\ s=\operatorname{flip}(s)$。

在单元素非空状态类型上，每个自映射都固定唯一元素；因此 `Bool` 是最小的非单点状态域反例。空状态类型因根本没有可写状态而属于退化治理接口，不作为这里的状态系统。

## 2.4 盲性设计律

由以上结果得到以下实现纪律：

1. 当前状态只出现在门的左侧，不出现在完整派生器的输入闭包中。
2. 若物理路径编码状态，loader 必须先把路径分解成稳定逻辑 ID 与独立状态坐标。
3. 派生器可以读取旧版本冻结状态，但必须显式携带严格版本先后证明。
4. 任何缓存键、基线选择或依赖闭包若由当前状态决定，都视为状态输入。
5. 一个“移动后派生结果改变”的测试，是盲性被破坏的直接反例：只改变 $h$ 时，$D$ 的结果应保持不变。

---

# 第三部　追加漂移与重键

## 3.1 内容地址、逻辑身份与结算分层

固定字节类型 $B$。字节串为 `List B`。

GFPT 的数学内容键直接定义为字节串本身：

$\kappa(b):=b$。

这样内容键在数学模型中天然无碰撞。实际实现若使用有限哈希值，必须另行提供适配条件：在当前受影响的规范字节集合上，哈希相等蕴含字节相等。GFPT 不假设任意现实哈希在无限输入域上全局单射。

内容条目包含：

- 稳定逻辑 ID $i:I$；
- 规范字节 $b:B^\ast$。

其内容键为 $\kappa(b)$。

结算状态不作为内容条目的可手改权威字段，而由独立的追加式结算事件折叠得到：

$\sigma:I\to\operatorname{Verdict}$。

活动地址同样由追加式激活、退役或重键事件折叠得到：

$a:I\to B^\ast$。

因此存在三个不同对象：

1. **历史内容条目**：可保留同一逻辑 ID 的多个历史字节版本；
2. **活动地址视图**：每个逻辑 ID 当前只指向一个内容键；
3. **结算视图**：每个逻辑 ID 的已结算判词。

活动地址和结算函数都是事件账本的语义投影，不是可与事件账本竞争的第二真源。若实现把它们物化到磁盘，必须从事件账重算并校验，不能允许手写漂移。

这一分层阻止两种混同：

- 改变地址不等于改变结算；
- 保留历史条目不等于同时激活两个真源。

## 3.2 追加式载体与尾节

对字节串 $x,y:B^\ast$，定义前缀扩展：

$x\preceq y\Longleftrightarrow\exists u:B^\ast,\ y=x\cdot u$。

对起点 $m\le |x|$，定义尾节 span：

$\operatorname{TailSpan}(x,m):=[m,|x|)$。

其字节为：

$\operatorname{Tail}(x,m):=\operatorname{drop}_m(x)$。

若 $y=x\cdot u$ 且 $m\le |x|$，则：

$\operatorname{Tail}(y,m)=\operatorname{Tail}(x,m)\cdot u$。

故：

$\operatorname{Tail}(x,m)\preceq\operatorname{Tail}(y,m)$。

这就是 **span 前缀扩展**。

若 $u$ 非空，则新尾节比旧尾节更长，精确字节内容键必然改变。该改变是追加式载体的正常结果，不应被诊断为旧字节遭篡改。

对账本历史 $H$，追加式更新同样写成 $H\preceq H'$。物理实现只允许向历史尾部追加新条目和重键事件；活动地址变化只是这些事件折叠后的视图变化。

## 3.3 尾节重键的适用类

不是所有前缀扩展都允许继承旧结算。重键只适用于由 schema 预先声明的 **尾节容器类**。

定义固定谓词：

$\operatorname{TailEligible}:I\to\operatorname{Prop}$。

该谓词必须由条目的不可变 kind 或类型确定，不能由当前手写状态、当前失败结果或“为了让本次通过”而临时确定。

普通定理陈述、普通数据记录或任意 prose span 若增加新字节，新增内容必须另行取得逻辑 ID 和结算；不得借尾节重键把新命题洗成旧 `admit`。

尾节重键只表达：

- 旧 span 字节完整保留为新 span 的前缀；
- 同一尾节容器的活动内容地址随追加而迁移；
- 旧结算事件完全不变；
- 新增后缀中的独立命题仍须单独 atomize 和裁决。

## 3.4 重键操作

给定：

- 旧文档 $x$ 与新文档 $y$；
- 尾节起点 $m$；
- 旧条目 $e$；
- 旧活动地址视图 $a$；
- 旧结算视图 $\sigma$。

合法重键结果记为：

$R(x,y,m,e,a,\sigma)=(e',a',\sigma',k_{\mathrm{pred}})$。

其条件为：

1. **资格**：$\operatorname{TailEligible}(e.\operatorname{id})$。
2. **追加**：$x\preceq y$ 且 $m\le |x|$。
3. **旧键规范**：$e.\operatorname{bytes}=\operatorname{Tail}(x,m)$。
4. **旧键现役**：$a(e.\operatorname{id})=\kappa(e.\operatorname{bytes})$。
5. **新条目规范**：$e'.\operatorname{id}=e.\operatorname{id}$ 且 $e'.\operatorname{bytes}=\operatorname{Tail}(y,m)$。
6. **谱系**：$k_{\mathrm{pred}}=\kappa(e.\operatorname{bytes})$，且 $e.\operatorname{bytes}\preceq e'.\operatorname{bytes}$。
7. **结算守恒**：$\sigma'=\sigma$。
8. **单活动源**：$a'$ 只在 $e.\operatorname{id}$ 处更新为 $\kappa(e'.\operatorname{bytes})$，其余逻辑 ID 不变。
9. **物理追加**：旧条目和旧事件不改字节；系统只追加 $e'$ 与从旧键到新键的重键事件。

条件 7 比“已 admit 不被翻转”更强：任何逻辑 ID 的结算都不因纯重键而改变。

条件 8 不删除历史。它只说明在新前缀的语义视图中，同一逻辑 ID 恰有一个活动内容键。旧键仍可由历史审计访问，但不再是当前活动源。

## 3.5 重键存在唯一性定理骨架

在以下前件下：

- 条目属于固定尾节类；
- $x\preceq y$；
- $m\le |x|$；
- 旧条目字节等于旧尾节；
- 旧活动索引确实指向旧键；

存在合法重键结果。

其构造被上述条件完全决定：

- 新条目 ID 取旧 ID；
- 新条目字节取 $\operatorname{Tail}(y,m)$；
- 前驱键取旧条目键；
- 新活动视图取单点更新；
- 新结算视图原样取 $\sigma$。

任意两个合法结果的全部字段逐项相等，故合法重键结果唯一。

因此有：

$\exists!r,\ \operatorname{LegalTailRekey}(x,y,m,e,a,\sigma,r)$。

## 3.6 保守性

合法重键蕴含：

- $\sigma'=\sigma$，故旧 `admit`、`reject` 和未决状态均不被翻转；
- 对目标逻辑 ID，活动源恰为新内容键；
- 对所有其他逻辑 ID，活动键不变；
- 旧内容字节和旧结算事件不变；
- 新增后缀不会自动继承旧结算为一个新命题；
- 同一输入产生同一重键结果，不存在人工选择第二键的自由度。

这一区分非常重要：

**重键继承的是逻辑容器的活动定位，不是后缀中新命题的证明。**

---

# 第四部　双律死锁与通道加法

## 4.1 修复类与放行集

固定修复动作类型 $M$。

令：

- $F\subseteq M$ 为待处理的精确修复类；
- $A\subseteq M$ 为规则一的放行集；
- $B\subseteq M$ 为规则二的放行集。

旧门的联合放行集为：

$L:=A\cap B$。

称修复类可达，当：

$\operatorname{Reachable}(F,A,B)\Longleftrightarrow\exists r\in F,\ r\in A\cap B$。

称修复类死锁，当：

$\operatorname{Deadlocked}(F,A,B)\Longleftrightarrow\neg\operatorname{Reachable}(F,A,B)$。

局部规则是否合理与修复类是否可达是两个问题。即使 $A$、$B$ 各自非空，各自排除了真实坏操作，它们仍可能在 $F$ 上没有共同放行元素。

## 4.2 双律死锁判据

有精确等价：

$\operatorname{Deadlocked}(F,A,B)\Longleftrightarrow F\cap(A\cap B)=\varnothing$。

该定理不需要分析规则文本的意图。只要把每条规则解释成实际放行集，死锁就是一个交集空性命题。

它也说明“所有已试路径都失败”只有在修复类和规则放行集被穷尽描述时才构成死锁证明。若路径矩阵漏掉一个动作，得到的只是采样失败，不是集合交为空。

## 4.3 保守通道加法

增加新通道 $C\subseteq M$，扩展后的总放行集为：

$L^+:=L\cup C$。

称 $C$ 是相对于死锁类 $F$ 的保守通道，当：

1. $L\subseteq L^+$；
2. $L^+\setminus L=F$。

第二项是精确边界：所有新增放行恰好属于 $F$，没有任何 $F$ 外动作因通道增加而变绿。

注意，规则一和规则二本身没有被修改。$A$ 仍是 $A$，$B$ 仍是 $B$。新增的是旧合取门旁的一条有名路径，不是把某条规则改成更宽的谓词。

## 4.4 保守通道存在性定理骨架

若 $F$ 在旧门下死锁，取：

$C:=F$。

因为 $F\cap L=\varnothing$，有：

$(L\cup F)\setminus L=F$。

故存在保守通道。

若进一步 $F\neq\varnothing$，则扩展门下至少有一个 $F$ 中动作可达；事实上所有 $F$ 中动作均可达。

该存在定理不证明任意指定的 $F$ 都安全。安全性来自 $F$ 的定义。尾节重键实例中，应取：

$F_{\mathrm{rekey}}:=\{\text{携带全部 `LegalTailRekey` 前件和规范结果的重键请求}\}$。

G-D—G-F 保证这个修复类中的动作存在、确定并保持结算。G-H 只证明可以把这一已经证明安全的类作为窄通道加入。

## 4.5 为什么通道不是豁免

合规实现应使用有类型分支，例如：

- `ordinary`：继续由规则 A 与规则 B 的合取判定；
- `tailRekey`：必须携带尾节资格、前缀扩展、规范旧键和保守结果证明。

不得实现成：

- `force = true`；
- “若 ingest 失败则忽略错误”；
- 按文件名或当前 issue 号跳过；
- 只要操作者声称是尾节就放行；
- 放宽 orphan 或 baseline-deletion 的全局定义。

通道加法的意义正是保留旧拒绝律对其他动作的全部检测能力。

---

# 第五部　证明义务清单

## 5.1 Canonical Lean 接口

建议定义落点：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.lean`

以下接口是 G-A—G-H 的唯一词汇表。实现时不得为同一概念另造可供下游二选一的同义谓词。

```lean
universe u v w

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

def Gate {Entry : Type u} {Status : Type v}
    (handwritten derived : Entry → Status) : Prop :=
  ∀ entry, handwritten entry = derived entry

abbrev BlindDeriver
    (Context : Type u) (Entry : Type v) (Status : Type w) :=
  Context → Entry → Status

abbrev SelfReadingDeriver
    (Context : Type u) (Entry : Type v) (Status : Type w) :=
  Context → (Entry → Status) → Entry → Status

def liftBlind
    {Context : Type u} {Entry : Type v} {Status : Type w}
    (d : BlindDeriver Context Entry Status) :
    SelfReadingDeriver Context Entry Status :=
  fun context _handwritten => d context

def StatusBlind
    {Context : Type u} {Entry : Type v} {Status : Type w}
    (D : SelfReadingDeriver Context Entry Status) : Prop :=
  ∃ d : BlindDeriver Context Entry Status, D = liftBlind d

def boolFlip : Bool → Bool
  | false => true
  | true => false

def PrefixExtension
    {Byte : Type u} (oldBytes newBytes : List Byte) : Prop :=
  ∃ suffix : List Byte, newBytes = oldBytes ++ suffix

def TailBytes
    {Byte : Type u} (document : List Byte) (start : Nat) :
    List Byte :=
  document.drop start

abbrev ContentKey (Byte : Type u) := List Byte

def contentKey
    {Byte : Type u} (bytes : List Byte) : ContentKey Byte :=
  bytes

inductive Verdict
  | pending
  | admit
  | reject
  deriving DecidableEq

abbrev Settlement (Id : Type u) := Id → Verdict

structure LedgerEntry (Id : Type u) (Byte : Type v) where
  logicalId : Id
  bytes : List Byte

def LedgerEntry.key
    {Id : Type u} {Byte : Type v}
    (entry : LedgerEntry Id Byte) : ContentKey Byte :=
  contentKey entry.bytes

abbrev ActiveIndex (Id : Type u) (Byte : Type v) :=
  Id → ContentKey Byte

def ActiveSource
    {Id : Type u} {Byte : Type v}
    (active : ActiveIndex Id Byte)
    (logicalId : Id) (key : ContentKey Byte) : Prop :=
  active logicalId = key

structure RekeyResult (Id : Type u) (Byte : Type v) where
  predecessor : ContentKey Byte
  newEntry : LedgerEntry Id Byte
  newActive : ActiveIndex Id Byte
  newSettlement : Settlement Id

def LegalTailRekey
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (result : RekeyResult Id Byte) : Prop :=
  tailEligible oldEntry.logicalId ∧
    PrefixExtension oldDocument newDocument ∧
    start ≤ oldDocument.length ∧
    oldEntry.bytes = TailBytes oldDocument start ∧
    ActiveSource active oldEntry.logicalId oldEntry.key ∧
    result.predecessor = oldEntry.key ∧
    result.newEntry.logicalId = oldEntry.logicalId ∧
    result.newEntry.bytes = TailBytes newDocument start ∧
    PrefixExtension oldEntry.bytes result.newEntry.bytes ∧
    result.newActive =
      Function.update active oldEntry.logicalId result.newEntry.key ∧
    result.newSettlement = settlement

def ConservativeRekey
    {Id : Type u} {Byte : Type v}
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (oldEntry : LedgerEntry Id Byte)
    (result : RekeyResult Id Byte) : Prop :=
  result.predecessor = oldEntry.key ∧
    result.newEntry.logicalId = oldEntry.logicalId ∧
    result.newSettlement = settlement ∧
    (∀ key,
      ActiveSource result.newActive oldEntry.logicalId key ↔
        key = result.newEntry.key) ∧
    ∀ logicalId,
      logicalId ≠ oldEntry.logicalId →
        result.newActive logicalId = active logicalId

def JointAllowed
    {Repair : Type u}
    (allow₁ allow₂ : Set Repair) : Set Repair :=
  allow₁ ∩ allow₂

def ReachableRepair
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) : Prop :=
  ∃ repair,
    repair ∈ repairClass ∧
      repair ∈ JointAllowed allow₁ allow₂

def Deadlocked
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) : Prop :=
  ¬ ReachableRepair repairClass allow₁ allow₂

def AllowedWithChannel
    {Repair : Type u}
    (allow₁ allow₂ channel : Set Repair) : Set Repair :=
  JointAllowed allow₁ allow₂ ∪ channel

def ConservativeChannel
    {Repair : Type u}
    (repairClass allow₁ allow₂ channel : Set Repair) : Prop :=
  JointAllowed allow₁ allow₂ ⊆
      AllowedWithChannel allow₁ allow₂ channel ∧
    AllowedWithChannel allow₁ allow₂ channel \
      JointAllowed allow₁ allow₂ = repairClass

end D5.S3.ConceptDynamics.GovernanceFixedPoint
```

上述 `Settlement` 与 `ActiveIndex` 是追加事件历史的语义视图。实现不得仅保存这两个函数而丢弃产生它们的事件来源。

以下代码块只冻结 theorem header；证明体由对应模块提供。理论卷不以 `sorry`、`axiom` 或伪占位符冒充证明。

## 5.2 G-A：状态盲门方程的唯一解

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/BlindGateUnique.lean`

精确陈述：

```lean
theorem status_blind_gate_has_unique_solution
    {Context : Type u} {Entry : Type v} {Status : Type w}
    (D : SelfReadingDeriver Context Entry Status)
    (hblind : StatusBlind D)
    (context : Context) :
    ∃! handwritten : Entry → Status,
      Gate handwritten (D context handwritten)
```

闭合路线只需消去 `StatusBlind` 的因子化见证、给出 `d context` 并使用函数外延。

禁止增加：

- `Fintype Entry`；
- `Nonempty Entry`；
- `DecidableEq Status`；
- 迭代收敛或有限状态前件。

## 5.3 G-B：两元素翻转无不动点

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/BooleanFlipNoFixedPoint.lean`

精确陈述：

```lean
theorem bool_flip_has_no_fixed_point :
    ¬ ∃ status : Bool, status = boolFlip status
```

闭合路线是对 `status` 的两个构造子分类。

该义务只证明一个最小非退化反例，不得加强成“所有非盲派生器均无不动点”。

## 5.4 G-C：尾节 span 保持前缀扩展

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension.lean`

精确陈述：

```lean
theorem tail_span_prefix_extension
    {Byte : Type u}
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (hprefix : PrefixExtension oldDocument newDocument)
    (hstart : start ≤ oldDocument.length) :
    PrefixExtension
      (TailBytes oldDocument start)
      (TailBytes newDocument start)
```

闭合路线是取得 `newDocument = oldDocument ++ suffix`，并证明：

`TailBytes newDocument start =
  TailBytes oldDocument start ++ suffix`。

不要求 `DecidableEq Byte`。

## 5.5 G-D：合法尾节重键存在

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence.lean`

精确陈述：

```lean
theorem legal_tail_rekey_exists
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (heligible : tailEligible oldEntry.logicalId)
    (hprefix : PrefixExtension oldDocument newDocument)
    (hstart : start ≤ oldDocument.length)
    (hbytes : oldEntry.bytes = TailBytes oldDocument start)
    (hactive :
      ActiveSource active oldEntry.logicalId oldEntry.key) :
    ∃ result : RekeyResult Id Byte,
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement result
```

规范见证必须逐字段构造，不使用任意选择：

- `predecessor := oldEntry.key`；
- `newEntry.logicalId := oldEntry.logicalId`；
- `newEntry.bytes := TailBytes newDocument start`；
- `newActive := Function.update active ...`；
- `newSettlement := settlement`。

新旧尾节的前缀关系必须经 G-C 得到，不能直接把欲证字段写成无来源假设。

## 5.6 G-E：合法尾节重键唯一

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness.lean`

精确陈述：

```lean
theorem legal_tail_rekey_unique
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    {first second : RekeyResult Id Byte}
    (hfirst :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement first)
    (hsecond :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement second) :
    first = second
```

闭合路线只允许：

- 消去两个合法性证明；
- 对 `LedgerEntry` 和 `RekeyResult` 做结构外延；
- 使用函数外延处理 `newActive` 与 `newSettlement`。

不得以哈希碰撞不可能作为额外公理；本卷的内容键已经是精确字节。

## 5.7 G-F：合法重键必保守

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative.lean`

精确陈述：

```lean
theorem legal_tail_rekey_is_conservative
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (result : RekeyResult Id Byte)
    (hlegal :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement result) :
    ConservativeRekey active settlement oldEntry result
```

闭合路线只用合法性字段及 `Function.update` 的同点、异点律。

该单命题必须同时通过 `ConservativeRekey` 的有名谓词表达：

- 谱系指向旧键；
- 逻辑 ID 不变；
- 整个结算视图不变；
- 目标逻辑 ID 只有一个活动键；
- 其他逻辑 ID 的活动键不变。

不得把“旧 admit 不翻”弱化成只检查一个示例状态。

## 5.8 G-G：双律死锁的交空判据

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion.lean`

精确陈述：

```lean
theorem deadlocked_iff_empty_joint_allowance
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) :
    Deadlocked repairClass allow₁ allow₂ ↔
      repairClass ∩ JointAllowed allow₁ allow₂ = ∅
```

闭合路线是展开 `Deadlocked` 与 `ReachableRepair`，再按集合成员关系证明双向蕴含。

不要求：

- `Repair` 有限；
- `Repair` 非空；
- 成员关系可判；
- 两条规则自身的放行集非空。

有限路径矩阵可作为该定理的 `Finset` 实例，但不能替代完整修复类的定义。

## 5.9 G-H：保守通道存在

建议模块：

`D5/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition.lean`

精确陈述：

```lean
theorem conservative_channel_exists
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair)
    (hdeadlocked :
      Deadlocked repairClass allow₁ allow₂) :
    ∃ channel : Set Repair,
      ConservativeChannel
        repairClass allow₁ allow₂ channel
```

闭合路线必须取显式见证：

`channel := repairClass`。

随后由死锁前件证明：

`AllowedWithChannel allow₁ allow₂ channel \
  JointAllowed allow₁ allow₂ = repairClass`。

不得改取 `Set.univ`，不得修改 `allow₁` 或 `allow₂`，不得把结论弱化成“至少放行一个未知动作”。

## 5.10 八条义务的原子性边界

G-A—G-H 满足以下共同纪律：

- 每条只有一个公开 theorem 结论；
- 每条可在一个独立 Lean 模块中闭合；
- 所有定义在 `Core.lean` 中预先固定；
- 不存在“选择合适定义使结论成立”的开放量词；
- 不依赖测度、概率、拓扑、统计显著性或解析估计；
- 不暗加 `Fintype`、`Nonempty` 或全局可判等号；
- 唯一额外类型类是重键所需的 `[DecidableEq Id]`；
- 有限失败见证优先使用 `Bool` 和 `List`；
- 不新增 axiom，不使用 `Classical.choice` 选择重键结果；
- 证明失败时应回灌为 statement revision，不能静默加强前件。

---

# 第六部　与 DECT 的关系

## 6.1 守卫自反在治理器上的实例

DECT 第 30 部的守卫自反要求新版本只引用已完成旧版本，禁止同层表达 $S=S(S)$。

GFPT 把这一纪律应用于状态校验器自身：

- 合法形式：当前状态由状态以外上下文和旧冻结前缀派生；
- 非法形式：当前候选状态参与自己的派生；
- 合法反射：$h_{n+1}=d(c_n,h_n^{\mathrm{frozen}})$；
- 非法同层自读：$h_{n+1}=D(c_n,h_{n+1})$。

G-A 是这一守卫在等号门上的最小不动点定理；G-B 是移除守卫后的有限反例。

## 6.2 接入科学六元循环

DECT 第 39 部的科学系统由 Define、Observe、Predict、Compare、Revise、Reflect 六个分量组成。

GFPT 不添加与其竞争的科学定义，而是刻画循环中治理状态的一个内层：

`Observe/ledger facts → Derive D → Gate G → reject reason → proof obligation → kernel settlement → guarded revision`。

在这一内层中：

- `D` 把已冻结事实归约为状态；
- `G` 检查表示是否忠实；
- 门拒绝不等于事实为假；
- 拒因必须转化为精确语义缺口；
- 缺口若来自同层自读，则修 D 的输入边界；
- 缺口若来自规则语言不足，则新增有名通道；
- 修订不得改写旧轮已经使用的判据和结算。

## 6.3 继承第 54、56、57 部的成功模式

GFPT 采用与 DECT 裁决层相同的闭合顺序：

1. 先记录真实失败矩阵；
2. 区分实现 bug、源陈述缺口和操作语言缺口；
3. 在理论卷中先固定类型、谓词和 theorem header；
4. 将大主张拆成单模块 elementary obligations；
5. 对拒因补充语义，而不是向原命题塞任意前件；
6. 每条义务分别送入 Lean 内核；
7. 证明失败则修订 statement；
8. 证明成功后以稳定 GID 落账；
9. 不复制已有冻结载体或谓词；
10. 结算注记只登记证明或收编映射，不重写旧段落。

因此本卷不是对两个 issue 的 prose 复盘，而是把两类失败转换为 G-A—G-H 八个可独立裁决的内核对象。

## 6.4 第 5″ 条的 harness 自反回灌

本卷是“以仓库已证科学方法研究仓库治理器”的直接实例。

具体回灌关系为：

- **前视承诺**：G-A—G-H 在证明前冻结，禁止证明完成后改成另一条更容易的命题。
- **盲核分解**：#3996 类故障不是继续搬运状态可消除的搜索残差，而是当前派生语言的结构性自读盲点。
- **预算包络纪律**：状态双向移动已穷尽两元素矩阵后，不继续支付重复试错预算；应改变派生接口。
- **追加目标不改旧结算**：重键不重算历史结算。
- **准入反单调**：治理器修改自己的派生或通道时，其自我裁决资格应收紧，并由独立门验证。
- **局部结算**：八条义务各有固定地址和单独终态，不能用“总体方向正确”替代逐条结案。

## 6.5 既有冻结定理的复用与禁重证

本卷明确复用以下既有冻结锚，不另造同义版本：

### `append_only_old_settlement_unchanged`

用途：证明向事件账追加新记录时，旧地址上的既有结算不被静默重算。

GFPT 不重复证明一般追加式结算守恒。G-F 只证明一个更局部的适配事实：`LegalTailRekey` 构造的重键结果根本不改变 `Settlement` 视图，并且只迁移一个活动地址。物理历史追加后，旧结算的全局守恒继续由既有冻结定理承担。

### `dependency_closure_admission_antitone`

用途：若修改重键通道或状态派生器的代理同时依赖这些被改对象，则其自我准入资格不能因任务紧急而放宽。

该定理不进入 G-A—G-H 的数学前件；它属于证明和合并流程的治理约束。

### `spectrum_commitment_local_settlement`

用途：把 G-A—G-H 各自按预登记地址和判据结算，不允许一个义务的证明替代另一个义务。

本卷不重新定义局部结算状态机。

### 其他冻结裁决定理

Pareto 弱支配、增益 cocycle、查表复制器和其他 DECT 冻结定理在 GFPT v1.0 中没有承重用途，因此不为“显得完整”而额外导入或重述。未来若需要比较多个通道的价值，应另作追加式增订。

## 6.6 `PrefixExtension` 不与 append-only 冻结族竞争

GFPT 的 `PrefixExtension` 是 `List` 上的局部字节关系，用于说明源 span 如何漂移。它不定义旧轮结算、不替代事件账语义，也不成为新的 append-only 真源。

两者的分工是：

- `PrefixExtension`：证明新源字节以旧源字节为前缀；
- `append_only_old_settlement_unchanged`：证明追加事件不改旧结算；
- `LegalTailRekey`：把前缀漂移转换为唯一活动地址迁移；
- `ConservativeChannel`：允许这一迁移类通过，而不放宽其他动作。

## 6.7 实现适配义务

将本卷接入实际 harness 时，还必须完成以下非 G-A—G-H 适配检查：

1. **状态擦除检查**：证明完整 loader 与 deriver 的组合通过状态擦除后的上下文因子化。
2. **别名审计**：状态目录、状态字段、bucket 和缓存键均不得回流 D。
3. **逻辑 ID 稳定性**：状态移动与纯重键不能改变条目的逻辑 ID。
4. **尾节资格闭包**：`tailEligible` 只能覆盖 schema 明确声明的尾节容器。
5. **哈希适配**：若现实键不是精确字节，证明受影响规范字节集合上的碰撞自由。
6. **事件单源**：活动索引和结算视图必须由事件账重算，不得成为手写第二真源。
7. **新增命题分离**：后缀中的新理论义务必须获得新逻辑 ID，不因容器重键继承旧 `admit`。
8. **通道窄化**：新通道只接受携带合法重键前件的请求。
9. **旧规则零改写**：orphan、baseline deletion 等既有规则的原放行集保持不变。
10. **独立裁决**：修改治理器的实现不得由同一依赖闭包中的实例单点自证。

这些是从抽象模型到具体仓库数据结构的桥。桥未完成时，只能声明 GFPT 内核定理已证，不能声明实际故障已修复。

---

# 边界与非冒领

GFPT v1.0 不作以下主张：

- 不声称所有治理死锁都可由增加通道解决；
- 不声称任何两个拒绝规则交为空就应增加通道；
- 不声称前缀扩展足以保持任意命题的语义；
- 不声称内容哈希在数学上无碰撞；
- 不声称状态盲派生器必然给出正确状态；
- 不声称非盲派生器必然失败；
- 不声称活动索引可以替代追加事件账；
- 不声称重键允许修改旧条目或旧结算；
- 不声称通道可按 issue、路径或操作者身份作临时豁免；
- 不声称八条义务已经 kernel 证毕。

本卷的精确结论边界是：

**状态派生对当前手写状态盲时，等号门良定且唯一；尾节内容在追加下发生前缀漂移时，存在唯一、不改结算、保持单活动源的规范重键；两条规则的合取封死该重键类时，存在只增加该类的保守通道。**

---

# 追加账本

## v1.0 — 2026-08-29

本版本追加存入：

- 治理系统、等号门、盲派生器和自读派生器；
- 完整流水线因子化意义下的状态盲性；
- 两元素翻转的无不动点模型；
- 内容键、逻辑 ID、结算视图和活动地址视图的分层；
- 字节前缀扩展、尾节 span 与 span 前缀扩展；
- `LegalTailRekey` 和 `ConservativeRekey`；
- 修复可达性、双律死锁、扩展门和保守通道；
- 八条精确证明义务 G-A—G-H；
- 与 DECT 守卫自反、科学六元循环及第 5″ 条的接线；
- 对既有 `append_only_old_settlement_unchanged` 等冻结定理的复用边界；
- 零 DECT 旧段落修改；
- 零既有冻结定理重证；
- 零测度、概率或拓扑前件；
- 零新增 axiom；
- 零证明完成冒领。

当前结算：

- G-A：`open`
- G-B：`open`
- G-C：`open`
- G-D：`open`
- G-E：`open`
- G-F：`open`
- G-G：`open`
- G-H：`open`

八条义务只有在对应 Lean 声明无 `sorry`、无新增私有公理并通过仓库冻结门后，方可逐条从 `open` 迁移为 `proved`。任何义务若因陈述错误被修订，应产生新稳定地址和显式映射；不得原地回写本卷 v1.0 的冻结陈述。
