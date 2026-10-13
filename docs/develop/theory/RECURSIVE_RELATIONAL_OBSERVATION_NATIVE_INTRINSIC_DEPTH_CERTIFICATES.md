# 原生内在深度证书：叶锥费用与二阶空间恢复阈值

## 1. 原树、当前读口与准确证书

**定义 1.1（原来源与内在深度）。** 来源域为全部非空有限自由有序满二叉树

$$
\mathcal T::=\alpha\mid\beta\mid(\mathcal T,\mathcal T).
$$

叶的不同出现、左右次序与括号均保留；不取结合律、交换律或共享子树商。固定

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=(\beta,\alpha),\qquad
\rho((S,T))=(\rho(S),\rho(T)),
$$

并令 $I_k=\rho^k[\mathcal T]$，其中 $I_0=\mathcal T$。复用 [JM §§36.2–36.3][JM] 的互斥像解析与唯一原始射线：每个 $T$ 唯一写成 $T=\rho^{\nu(T)}P(T)$，其中 $P(T)\notin I_1$，且

$$
\nu(T)=\max\{k\in\mathbb N_0:T\in I_k\}.
\tag{NIC.1}
$$

因此最大值有限，$T\in I_k$ 当且仅当 $\nu(T)\ge k$。这里 $\nu$ 是当前树的最大逆生成深度。它没有指定实际入口、入口后的替换次数、读取次序或物理时间。

**定义 1.2（四值字面读口）。** 令 $\mathcal A$ 为全部有限 $L/R$ 字，根地址为 $\varepsilon$，拼接写作 $pq$。对每个 $T\in\mathcal T$ 与 $q\in\mathcal A$，原始回复 $r(q,T)$ 属于 $\{\alpha,\beta,\mathsf{br},\mathsf{abs}\}$，递归规定为

$$
\begin{aligned}
r(\varepsilon,\alpha)&=\alpha,&
r(\varepsilon,\beta)&=\beta,&
r(\varepsilon,(S,T))&=\mathsf{br},\\
r(Lq,(S,T))&=r(q,S),&
r(Rq,(S,T))&=r(q,T),\\
r(cq,\alpha)&=\mathsf{abs},&
r(cq,\beta)&=\mathsf{abs}\qquad(c\in\{L,R\}).
\end{aligned}
\tag{NIC.2}
$$

每个有限字均可直接请求，无须先请求其祖先。此口与 [JM §28.1][JM]、[ActualTreeReadoutAcquisition 的 Address、Reply、readout][Readout] 相同；Lean 载体中 false 表示 $L$，true 表示 $R$，叶 true 表示 $\alpha$，叶 false 表示 $\beta$。配对与 $\rho$ 是输入树的数学生成运算，不是此读口供应的源编辑权限。

**假设 1.3（实际取得合同）。** 一段历史的全部回复真实，来自同一棵不可变的当前树 $T$ 与同一纪元。观察者从共同的来源无关初态开始，仅可作 $\mathrm{Read}(q)$、付费本地计算与普通停止。它不预先收到完整树、完整叶词、尺寸、生成次数、真实入口或自底向上的来源流。来源与纪元的一致性是合同条件，不是一个免费可读的身份标签。实际写入、访问、解析和保留自己的历史，以及任何数值输出接口，均须另行供应并付费。

**定义 1.4（实际历史的全域纤维）。** 有限、按读取次序排列的历史为

$$
h=((q_1,y_1),\ldots,(q_m,y_m)),\qquad
y_i=r(q_i,T).
$$

允许重复地址。记

$$
\begin{aligned}
A=\operatorname{paid}(h)&=\{q_i:1\le i\le m\},\\
\mathcal S(h)&=\{U\in\mathcal T:\forall i,\ r(q_i,U)=y_i\}.
\end{aligned}
\tag{NIC.3}
$$

若 $\forall U\in\mathcal S(h),\ \nu(U)=\nu(T)$，则称 $h$ 为 $T$ 的准确深度证书。竞争者始终是全部 $\mathcal T$：没有叶数、组成、词、深度、正成员或替换像许诺。顺序属于实际取得历史；$\mathcal S(h)$ 只检验全部已取得原始回复的合取。确定控制器从共同初态重放相同回复时也作相同请求和停止决定，这一对应复用 [JM §28.3][JM] 与 [Readout 的 source_foundation 证明中的 replay][Readout]。

## 2. 未触及叶锥中的原始竞争者

**定义 2.1（前沿与锥）。** 当前树的真实叶地址集递归为

$$
F(\alpha)=F(\beta)=\{\varepsilon\},\qquad
F((S,T))=LF(S)\cup RF(T).
$$

令

$$
N(T)=|F(T)|,\qquad
\Lambda(T)=\sum_{p\in F(T)}|p|,\qquad
\operatorname{Cone}(p)=\{pw:w\in\mathcal A\}.
\tag{NIC.4}
$$

$|p|$ 是地址的方向字母数，$|\varepsilon|=0$。$\operatorname{Cone}(p)$ 包含 $p$ 本身及它的全部字面后代；对实际叶，严格后代的当前回复均为缺席。$F(T)$ 是非空有限前缀无关集，所以不同真实叶的锥两两不交。地址负载也可记为 $L(T)$；本卷使用 $\Lambda(T)$，以免与方向字母 $L$ 混淆。

**定理 2.2（原始叶锥竞争者）。** 对每个 $T\in\mathcal T$、每个 $p\in F(T)$，把该叶替换为有序二叶树 $(\alpha,\beta)$，其余节点保持原样，得到数学比较输入 $T[p\leftarrow(\alpha,\beta)]$。则

$$
\nu(T[p\leftarrow(\alpha,\beta)])=0
\tag{NIC.5}
$$

且对每个 $q\notin\operatorname{Cone}(p)$，

$$
r(q,T[p\leftarrow(\alpha,\beta)])=r(q,T).
\tag{NIC.6}
$$

证明。复用 [JM §36.2][JM] 的一阶像语法

$$
I_1::=\beta\mid(\beta,\alpha)\mid(I_1,I_1).
$$

其必要局部条件是：每个 $\alpha$ 叶必须是一个终端 $(\beta,\alpha)$ 的右孩子；特别地，一阶像不能有左孩子为 $\alpha$ 叶的节点。这也正是 [Readout 的 alphaValid 与 source_foundation 的一阶有效性供应][Readout] 的相应局部内容。替换树在地址 $p$ 处具有左孩子为 $\alpha$ 的节点，不满足该必要条件，故不在 $I_1$。由 (NIC.1) 得 (NIC.5)。

对 $q\notin\operatorname{Cone}(p)$ 分两类。若 $q$ 是 $p$ 的严格前缀，则它是原叶的严格祖先，替换前后都为分支。否则 $p,q$ 在某个位置分别进入不同孩子，此后 $q$ 所访问的子树完全未变；如果它在该子树中缺席，仍然缺席。这覆盖全部不延伸 $p$ 的字面地址，给出 (NIC.6)。当 $p=\varepsilon$ 时锥为全部 $\mathcal A$，(NIC.6) 的量词域为空，(NIC.5) 仍成立。比较输入都是合法有限原树；这里没有在实际只读来源上执行替换。$\square$

## 3. 每个正深度的准确费用基线

**定义 3.1（静态证书费用）。** 对固定 $T$ 与有限 $B\subseteq\mathcal A$，取它在 $B$ 上的全部真实回复。若这些回复在全部 $\mathcal T$ 上强制 $\nu(U)=\nu(T)$，称 $B$ 为静态准确深度证书，其费用向量为

$$
c(B)=\left(|B|,\ \sum_{q\in B}|q|\right).
\tag{NIC.7}
$$

这是两个分别比较的坐标，没有把它们换成物理持续时间或存储量。静态优化中的 $B$ 可以依赖所分析的 $T$；这不把 $B$ 作为未知来源读者的初始输入。实际历史的静态费用取 $B=\operatorname{paid}(h)$。

**定理 3.2（正深度的叶锥下界及同时达到）。** 对每个 $\nu(T)\ge1$ 的 $T$ 与每个来自 $T$ 的有限准确深度证书 $h$，其不同地址集 $A$ 满足

$$
\forall p\in F(T),\quad A\cap\operatorname{Cone}(p)\ne\varnothing,
\tag{NIC.8}
$$

从而

$$
|A|\ge N(T),\qquad
\sum_{q\in A}|q|\ge\Lambda(T).
\tag{NIC.9}
$$

$F(T)$ 的全部带标签回复强制整个原树为 $T$，因此同时达到两个下界。全部静态准确深度证书的最小费用向量恰为

$$
\bigl(N(T),\Lambda(T)\bigr).
\tag{NIC.10}
$$

若某个准确证书同时取等号，则它的不同地址集恰为 $F(T)$。

证明。若存在 $p\in F(T)$ 使 $A$ 不接触其锥，定理2.2的原始竞争者在 $A$ 的每个地址给相同回复，故属于 $\mathcal S(h)$；它的深度为零，而 $\nu(T)\ge1$，违反准确性。这证明 (NIC.8)。

为每个叶 $p$ 选择一个 $q_p\in A\cap\operatorname{Cone}(p)$。叶锥两两不交，故 $p\mapsto q_p$ 单射；又 $q_p=pw_p$，所以 $|q_p|\ge|p|$。因此

$$
|A|\ge|\{q_p:p\in F(T)\}|=N(T),
\qquad
\sum_{q\in A}|q|
\ge\sum_{p\in F(T)}|q_p|
\ge\sum_{p\in F(T)}|p|.
$$

上界使用既有完整前沿刚性：[JM §28.3][JM] 与 [Readout 的 source_foundation][Readout] 已证明，对任意原树 $V,U$，若 $U$ 匹配 $V$ 的每个叶地址及标签，则 $U=V$。代入 $V=T$ 与查询集 $F(T)$ 即得准确深度，并恰有 (NIC.10) 的费用；完整树证书的这一上界不计作新增恢复定理。

若同时取等号，基数等号先给 $A=\{q_p:p\in F(T)\}$。负载等号使每个非负整数 $|q_p|-|p|$ 为零；拼接长度可加，所以每个 $w_p=\varepsilon$，即 $q_p=p$。于是 $A=F(T)$，包括根为单叶的情形。$\square$

支持必须命中可区分竞争者的论证方法复用 [JM §53.2][JM]；本定理的来源内增量是定理2.2所给的一阶原始叶锥竞争者，以及由其不交锥得到的全部正深度双坐标基线。固定词证书的竞争域不同，不能将 [JM §§53–63][JM] 的单色或同词最优数直接代入 (NIC.9)。

## 4. 二阶像的每个叶标签都承重

**定理 4.1（二阶单叶翻转障碍）。** 对全部 $T\in I_2$ 与全部 $p\in F(T)$，令 $\operatorname{flip}_p(T)$ 只交换地址 $p$ 的 $\alpha/\beta$ 标签，保持全部括号及其他标签。则

$$
\operatorname{flip}_p(T)\notin I_2,\qquad
\nu(\operatorname{flip}_p(T))\le1.
\tag{NIC.11}
$$

证明。复用 [Readout 的 source_foundation][Readout] 的两个低阶局部必要条件：一阶像中每个 $\alpha$ 叶是终端 $(\beta,\alpha)$ 的右孩子；二阶像中每个终端二叶节点的标签恰为 $(\beta,\alpha)$。后者对应 cherryValid 在每个 $\rho^2S$ 上为真，前者对应 alphaValid 在每个 $\rho S$ 上为真。$I_2\subseteq I_1$，所以二阶像同时服从两条件。

写 $T=\rho^2S$。对原树 $S$ 的每个叶出现，两次替换给以下两种完整块：

$$
C=\rho^2\alpha=(\beta,\alpha),\qquad
D=\rho^2\beta=((\beta,\alpha),\beta)=(C,\beta).
\tag{NIC.12}
$$

$\rho$ 保有序配对，故 $\rho^2S$ 由 $C,D$ 按 $S$ 的括号配对。归纳于 $S$，每个当前叶都处于某个这样的块内；原叶块的地址锥不交，因此只需检查该叶所属块。

在 $C$ 内，翻左叶得到 $(\alpha,\alpha)$，翻右叶得到 $(\beta,\beta)$；两者都使该终端节点违反二阶终端标签条件。在 $D=(C,\beta)$ 内，翻 $C$ 中的任一叶仍产生上述终端违例。剩下一种是翻 $D$ 的右 $\beta$，所得 $(C,\alpha)$ 的右 $\alpha$ 叶，其左兄弟是分支 $C$，不是叶 $\beta$，违反一阶的 $\alpha$ 伴随条件。全部违例都位于块内部，保持块以上的括号并接入任意外部原树不会消除它们。

因此任何一个叶的翻转都违反 $I_2$ 的必要条件，得到第一式。第二式由 (NIC.1) 与自然数深度得到。本证明不使用三阶正成员翻叶障碍。$\square$

**定理 4.2（准确深度的二阶单点阈值）。** 对全部 $\nu(T)\ge2$ 的原树 $T$ 与全部来自 $T$ 的有限真实历史 $h$，若 $A=\operatorname{paid}(h)$，则

$$
\begin{aligned}
h\text{ 准确认证 }\nu(T)
&\quad\Longleftrightarrow\quad F(T)\subseteq A\\
&\quad\Longleftrightarrow\quad \mathcal S(h)=\{T\}.
\end{aligned}
\tag{NIC.13}
$$

特别地，在此深度范围内，一个非单点的原始证据纤维不能准确认证内在深度；仅查询每个叶的严格后代不能代替查询叶标签。

证明。若 $p\in F(T)\setminus A$，既有单叶翻转的原始回复不变性说明

$$
\forall q\ne p,\quad
r(q,\operatorname{flip}_p(T))=r(q,T).
$$

这是 [Readout 的 source_foundation][Readout] 的相应因子，也是 [JM §28.3][JM] 的单点反向证明：祖先仍是分支、后代仍缺席、其他支路及叶未变。因此 $\operatorname{flip}_p(T)\in\mathcal S(h)$。由定理4.1，它的深度至多一，与 $\nu(T)\ge2$ 不同。准确深度遂强制 $F(T)\subseteq A$。

若包含全部真实叶，则全部候选匹配整个带标签前沿；复用同一完整前沿刚性即得 $\mathcal S(h)=\{T\}$。单点自然强制深度准确。最后，叶翻转只改变 $p$ 本身的回复，所有严格后代在两个来源中都缺席，所以任何数目的这类后代请求都不能排除该竞争者。$\square$

定理4.2在 $\nu(T)\ge3$ 的部分也可直接由既有三阶障碍取得：$T\in I_3$，单叶翻转不在 $I_3$，于是深度不同。[Readout 的 source_foundation][Readout] 与 [ActualImageAddressCertificate 的 rigidity][ImageCert] 已供应该范围；后者的无组成许诺证书参数为 $d=3k,\ k\ge1$。本节扩展所依赖的是定理4.1的 $I_2$ 障碍，而不是重述这些三阶供应。

## 5. 深度一的实际例外与后继请求

**定理 5.1（四次实际读取留下准确的双树纤维）。** 取两个合法原来源

$$
U=((\beta,\alpha),(\beta,\beta)),\qquad
V=((\beta,\beta),(\beta,\beta)),
\tag{NIC.14}
$$

以及固定顺序的请求 $LL,LRL,RL,RR$。这组来源无关请求在两个来源上都取得同一真实历史

$$
h_*=\bigl((LL,\beta),(LRL,\mathsf{abs}),(RL,\beta),(RR,\beta)\bigr).
\tag{NIC.15}
$$

其全部原树纤维、深度与构造坐标满足

$$
\mathcal S(h_*)=\{U,V\},\qquad
\nu(U)=\nu(V)=1,\qquad Q(U)=Q(V)=(1,0).
\tag{NIC.16}
$$

其中 $Q=(\nu,e)$ 与 $e(T)=1\iff P(T)=\alpha$ 按 [JM §§49–50][JM] 原定义使用。两来源各有四个真实叶，叶地址恰为 $\{LL,LR,RL,RR\}$，所以

$$
N(U)=N(V)=4,\qquad
\Lambda(U)=\Lambda(V)=8,
$$

而

$$
|\operatorname{paid}(h_*)|=4,\qquad
\sum_{q\in\operatorname{paid}(h_*)}|q|=9,\qquad
LR\notin\operatorname{paid}(h_*).
\tag{NIC.17}
$$

因此四读历史达到不同地址数的准确深度下界，却没有达到地址负载下界，也不是完整空间证书。

证明。$LL=\beta$ 迫使根及左孩子均为分支，左左孩子恰为 $\beta$。由于原树为满二叉树，$LR$ 已到达。$LRL=\mathsf{abs}$ 排除 $LR$ 为分支：若它是分支，其左孩子必存在，回复不可能缺席。因此 $LR$ 恰为一个叶，标签尚可为 $\alpha$ 或 $\beta$。$RL=RR=\beta$ 同时强制右孩子为分支，两个孩子恰为 $\beta$。所以候选恰为 (NIC.14) 的两个，没有任何尺寸或标签许诺被加入竞争域。

两树的一阶前像为

$$
U=\rho\bigl((\beta,(\alpha,\alpha))\bigr),\qquad
V=\rho\bigl(((\alpha,\alpha),(\alpha,\alpha))\bigr).
$$

两个前像都有左孩子为 $\alpha$ 叶的节点，不在 $I_1$。复用唯一像解析及原始射线，得两树深度恰为一，其原始端点分别就是所列前像；均不是 $\alpha$，故标志 $e=0$。这也可由右子树的终端 $(\beta,\beta)$ 直接排除二阶像。$Q$ 的这一计算仅应用已有坐标定义，不另认领新的 $Q$ 合成律。

四个叶都在地址长度二处，前沿负载为八。四个实际请求的长度依次为二、三、二、二，合计九，且互异。定理3.2对两来源给不同地址数至少四，故 (NIC.15) 取到此坐标的最小值。$U\ne V$ 且 $LR$ 未读，证明其非单点及未取得完整前沿。$\square$

**假设 5.2（数值消费者与完整接管）。** 数值输出不由原 Boolean 停止位编码。若要交付 $\nu$，另供共同、来源无关、仅消费实际保留证据的本地消费者 $\Delta_\nu$；其程序、计算与输出付费。若有后继任务，另供新任务入口，并要求同一来源与同一纪元继续静止、证据真实可访问。任何切口都明确全部仍可访问的信息；不能把未声明的工作区、计时、来源标签或档案区别作为隐藏证据。

**定理 5.3（实际可取得的深度边界及一次后继区别）。** 在假设1.3与5.2的付费本地计算、保留及消费者合同下，存在一个共同的全原树有限取得程序：原停止位交付 $\operatorname{Pos}(T)\iff T\in I_3$，另行供应的 $\Delta_\nu$ 准确交付 $\nu(T)$。在 $U,V$ 上它只作 (NIC.15) 的四次读取，并可保留该双树证据而停止。

若后继任务为在同一当前来源上输出 $r(LR,T)$，且交接后全部来源相关可访问信息仅为 $h_*$、其任何共同确定后处理，或准确的 $\nu,Q$，则不存在对 $U,V$ 都准确的零新增读取消费者。一次新增原始请求 $\mathrm{Read}(LR)$ 足以区分；它的字面地址长度为二。

证明取得。共同程序先请求 (NIC.15) 的四个固定字面地址。若实际回复恰为该模式，定理5.1强制当前来源为 $U$ 或 $V$，深度均为一；普通停止位输出零，$\Delta_\nu$ 从保留的模式输出一。此程序的初态与公共请求列表完全不依赖未知来源。

若任一回复不符合该模式，使用 [Readout 的 acquisitionStep、acquisitionTrace、restore、acquisition_foundation][Readout] 所供应的同口完整取得：待访列表先含根，读到分支才加入两个孩子，叶不展开；有限原树的全部节点访问完毕后，由实际取得前沿恢复当前树。随后有限逆解析计算深度，并返回原成员位。旧四读记录可保留；后备的重复请求与额外工作另计。这一支的有限性和完整恢复直接复用既有取得供应，不主张新的遍历最优性。消费者是共同程序：模式成功时返回一，否则仅解析真实完整取得记录并取其深度。由两支的正确性，它对全部 $\mathcal T$ 有限且准确。数值不是从原停止位零反推出来的。

证明后继障碍。直接由 (NIC.14)，

$$
r(LR,U)=\alpha,\qquad r(LR,V)=\beta.
\tag{NIC.18}
$$

假设所列交接信息在两输入上完全相同。任何不再访问来源的确定消费者，从相同接管配置及相同公共任务 $LR$ 开始，只作相同本地计算并返回同一值；不能同时满足 (NIC.18)。对相同信息的更多确定后处理也不会形成新区别。实际查询 $LR$ 的两个真实回复恰为 (NIC.18)，所以一次新增读足够。推导数值或模拟出的回复都不是新的 raw 事件收据；若任务要求一条实际 $\mathrm{Read}(LR)$ 收据，该事件仍须实际发生。$\square$

此例将定理4.2的阈值定在二：深度一可以由非单点、实际取得且保留的原始边界准确认证，随后却不能服务一个尚未得到区别的原生地址任务。已有 $Q$ 上下文同余只保证 [JM §50.1][JM] 的配对与 $\rho$ 构造上下文中的深度任务；$LR$ 的原始回复不属于那个终端任务域。

## 6. 恢复接口与资源坐标

**定义 6.1（同纪元后继值任务）。** 对来源 $T$，后继值任务的参数域为全部有限 $q\in\mathcal A$，目标为数值 $r(q,T)$，而非实际读取事件收据。当定理4.2的历史已准确认证某个 $\nu(T)\ge2$，并在假设5.2的完整接管下保留且可访问时，它含有每个真实叶的实际标签回复。因此可接用 [JM §28.3][JM] 的前沿解析，恢复 $T$，再由 (NIC.2) 付费计算任何有限 $q$ 的值，不需要新的来源读取。这里保留、接管、解析、计算与输出是明确前提；“证据纤维单点”本身不安装一个能访问旧历史的消费者。定理5.3给深度一时同一后继任务域中的具体失败行。

**定义 6.2（分别收费的坐标）。** 对 $h$ 定义不同地址负载与实际请求负载

$$
\begin{aligned}
C_{\rm distinct}(h)&=|\operatorname{paid}(h)|,&
W_{\rm distinct}(h)&=\sum_{q\in\operatorname{paid}(h)}|q|,\\
C_{\rm calls}(h)&=m,&
W_{\rm transmitted}(h)&=\sum_{i=1}^{m}|q_i|.
\end{aligned}
\tag{NIC.19}
$$

定理3.2只精确优化前两项。后两项计入每次实际重复请求及其完整地址字母；地址压缩或共享前缀传输若另有编码合同，须单独定价。峰值记忆、压缩后的保留长度、临时计算工作、证据寿命、停止与数值输出费用也各自是另一个坐标。完整根遍历每个实际节点一次；一个 $N$ 叶满二叉树有 $N-1$ 个分支，故该既有取得程序用 $2N-1$ 个不同节点请求。这是通用达到供应，不声称未知来源发现的最优数为 $N$ 或 $2N-1$。

**假设 6.3（前向呈示及真实入口须另供）。** 若以后要跨版本使用本卷边界，须另供真实同源前向更新合同、更新或滞后信息、各当前读取段的静止性、证据版本对应与全部保留隔离条件，并分别计费。没有这些条件，旧叶地址及标签不能被当成新版本的 raw 回复。若要恢复实际入口和入口后的替换次数，也须另有真实入口记录；[JM §§37.1–37.5][JM] 的当前源不可区分性仍适用。本卷的 $\nu(T)$、实际取得序号 $i$、$\mathrm{Read}$ 次数、字面地址长度、入口后替换次数与物理持续时间属于不同变量，不互相定义。

**定理 6.4（正深度假设不能删去）。** 取 $T=(\alpha,\alpha)$ 与单读历史 $h=((L,\alpha))$。则 $h$ 准确认证 $\nu(T)=0$，但

$$
\operatorname{paid}(h)\cap\operatorname{Cone}(R)=\varnothing,\qquad
|\operatorname{paid}(h)|=1<N(T)=2.
\tag{NIC.20}
$$

证明。全部匹配原树恰为 $\{(\alpha,W):W\in\mathcal T\}$：非空地址 $L$ 的叶回复强制根为分支且左孩子为 $\alpha$，对右孩子没有约束。每个这样的树都有左 $\alpha$ 叶，违反一阶像必要条件，所以全部深度为零。实际 $T$ 是其中一个，故证书准确，却不接触右叶锥，且只读一个地址。$\square$

## 7. 数学供应与结论范围

**约定 7.1（归属及文献条件）。** 本卷定理2.2、3.2、4.1、4.2、5.1、5.3与6.4按 repo-derived 的普通推导使用。它们的来源内机制分别为原始叶锥竞争者、正深度的双坐标最小费用、二阶翻叶障碍、二阶单点阈值以及实际深度一例外。完整前沿刚性、全原树遍历、三阶正成员叶必要性、唯一像解析、原始射线、$Q$ 的配对与构造上下文商以及真实入口不可取得性，均按上述原归属作为供应，不计新增数学内容。定理5.3使用的实际保留和后来操作合同与 [SLH §§53–54、59–64、69–75][SLH] 的来源、证据与后继任务区分相容；这里没有重建其一般保留纤维理论。

$Q$ 所用单孔代入同余的成熟背景是 Dexter Kozen, *On the Myhill–Nerode Theorem for Trees*, Bulletin of the EATCS 47, 170–173，作者[原文][Kozen]。其 PDF 第2–3页定义有限 ranked alphabet 的 ground terms、同余与确定自底向上树自动机，第3–5页给单变量一次出现的代入关系及有限指数条件。这一背景属 literature-attested；将两个叶映为两个零元符号、配对映为二元符号即可对应原树载体。该文不供应原生字面地址取得口、(NIC.8) 的替换锥竞争者、地址费用、非恒定 $\nu$ 的取得程序或真实入口记录。本文不据此把无限 $Q$ 坐标像称为有限状态实现，也不作外部原创性判断。

**约定 7.2（任务域不互换）。** (NIC.8)–(NIC.13) 的正确域是全部原树匹配原始回复的纤维；没有固定词、组成或像许诺。定理5.3的后继比较域则是已经实际取得 (NIC.15)、且满足完整接管的两个当前来源；不是缩小前述证书的全域量词。$\nu$ 或 $Q$ 的事后数值充分性，不等于该数值已被取得；一个静态最优地址集，不等于未知源读者已知道该地址集；完整保留的历史，不等于最小或免费记忆。上述原始证书结论既不决定通用发现策略的最优费用，也不提供跨版本时钟、写入、构造或新的来源事件接口。

[JM]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[Readout]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ImageCert]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate.lean
[SLH]: https://github.com/the-omega-institute/trureturing/blob/782ca801d00c48d48e3b08553333b786bcf3e65e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[Kozen]: https://www.cs.cornell.edu/~kozen/Papers/mn.pdf

## 追加锚（本行以下为增补区）

## 8. 深度余数语境与插入常数的材料

**定义 8.1（原来源上的坐标供应）。** 沿用定义1.1的全部非空有限自由有序树、同一个 $\rho$、唯一原始端点 $P(t)$ 及深度 $\nu(t)$。置

$$
T_j=\rho^j\alpha,\qquad
e(t)=\mathbf 1_{\{P(t)=\alpha\}},\qquad Q(t)=(\nu(t),e(t)).
$$

标志一的深度 $j$ 来源恰为实际树 $T_j$；标志零称为非射线来源。使用 [JM §§36、49–50][JM] 的原定义及 [IntrinsicSubstitutionCoordinates 的 all_source_coordinate_law][ISC]，若 $Q(s)=(a,e)$、$Q(t)=(b,f)$，则

$$
\begin{aligned}
Q(\rho t)&=(\nu(t)+1,e(t)),\\
Q((s,t))&=
\begin{cases}
(b+2,1),&e=f=1\ \text{且}\ a=b+1,\\
(\min(a,b),0),&\text{其他情形}.
\end{cases}
\end{aligned}
\tag{NIC.21}
$$

称第一种配对为例外配对。两个叶的坐标分别为 $(0,1)$、$(1,1)$；标志不是当前叶标签。记 $\ell(t)=N(t)$，并沿用 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。[JM 命题37.4][JM] 的组成运输同时供应

$$
\ell(T_j)=F_{j+1},\qquad
\nu(c)=j\Longrightarrow\ell(c)\ge F_{j+1}.
\tag{NIC.22}
$$

这些是本节的已有前提，不另立原始射线、配对律或 Fibonacci 增长定理。

**定义 8.2（单孔语境与三项资源）。** 语境仍取 [JM 定义50.1][JM] 的原语法

$$
C::=\square\mid\rho C\mid(C,c)\mid(c,C),\qquad c\in\mathcal T.
\tag{NIC.23}
$$

孔出现一次。每个 $c$ 是完整实例化的实际有限原树，其全部叶出现、左右次序与括号均保留。定义孔路径配对数 $b(C)$、插入材料 $\mu(C)$ 及常数深度上界 $M(C)$：

$$
\begin{aligned}
b(\square)&=0,&\mu(\square)&=0,&M(\square)&=0,\\
b(\rho C)&=b(C),&\mu(\rho C)&=\mu(C),&M(\rho C)&=M(C),\\
b((C,c))&=b((c,C))=b(C)+1,\\
\mu((C,c))&=\mu((c,C))=\mu(C)+\ell(c),\\
M((C,c))&=M((c,C))=\max(M(C),\nu(c)).
\end{aligned}
\tag{NIC.24}
$$

$b$ 不数常数内部的配对，$\mu$ 则数每次插入的完整常数树的全部叶。同一树写在两个常数位置就计两次；没有共享商。$M=0$ 的无常数语境与只有深度零常数的语境可由 $b$ 区分。

在不含一元 $\rho$ 的语境上，$\mu$ 正是 [ActualLeafHistoryRigidity 的 OutputContext.outsideLeaves][ALHR]：孔路径上实际旁支的叶数之和。含 $\rho$ 时，(NIC.24) 只记各常数插入时的材料，不记其后外层替换增加的叶数；它不是最终树的孔外叶数、替换次数、压缩描述长度、地址费用或运算费用。这一定义没有把一元替换定价为免费。

**定义 8.3（余数分离与有界配对测试）。** 固定整数 $m\ge2$，终端观察为

$$
o_m(t)=\nu(t)\bmod m.
$$

若 $o_m(C[s])\ne o_m(C[t])$，称 $C$ 分离 $s,t$。记

$$
s\sim_{m,k}t
\quad\Longleftrightarrow\quad
\forall C\text{ 满足 (NIC.23) 且 }b(C)\le k,
\quad o_m(C[s])=o_m(C[t]).
\tag{NIC.25}
$$

$\sim_{m,\infty}$ 表示对全部有限语境量化，没有无穷表达式。每个比较都将同一个语境、相同实际常数与相同运算次序代入两来源。对 $b$ 的限制不限制常数尺寸、常数内部配对或一元替换次数。

模数条件保留 $m\ge2$；若 $m=1$，则全部来源及全部语境的终端余数按定义恒为零，没有分离语境。

## 9. 同深度相反标志的尖锐分离费用

**定理 9.1（首次配对的全部存活情形）。** 设 $Q(s)=(n,1)$、$Q(t)=(n,0)$。沿任一分离语境的孔路径从孔向外计算。首次配对前若经过 $v$ 次 $\rho$，置 $j=n+v$。首次配对必须属于且只可能属于下列两类；表中坐标顺序为 $s,t$：

$$
\begin{array}{c|c|c}
\text{首次配对}&\text{必要实际常数}&\text{配对后坐标}\\\hline
(\rho^v\square,c)&c=T_{j-1},\ j\ge1&(j+1,1),\ (j-1,0)\\
(c,\rho^v\square)&c=T_{j+1}&(j+2,1),\ (j,0)
\end{array}
\tag{NIC.26}
$$

其余首次配对都会使两个 $Q$ 坐标相同，后续任意有限语境均无法再分离。只有一次孔路径配对的语境在这两个输入上总给相同奇偶深度。

证明。首次配对前，(NIC.21) 给 $(j,1),(j,0)$。非射线输入不能作例外配对，其结果总为 $(\min(j,\nu(c)),0)$。若射线输入也不作例外配对，两个结果完全相同；[JM 定理50.2证明中的坐标稳定性][JM] 或 (NIC.21) 的直接逐构造应用说明，全部后续操作保持这种相同。

所以射线输入必须作例外配对，且 $e(c)=1$。孔在左边时要求 $j=\nu(c)+1$，故 $j\ge1,c=T_{j-1}$；孔在右边时要求 $\nu(c)=j+1$，故 $c=T_{j+1}$。(NIC.21) 分别给出 (NIC.26)。无配对语境只在相同深度上加相同整数。一次配对语境在表列存活情形的深度差恰为二，外层任意次数 $\rho$ 不改变该差；其他情形深度差为零。因此全部这类奇偶测试相同。$\square$

**定理 9.2（相反标志的最小配对数与最小材料）。** 设 $Q(s)=(n,1)$、$Q(t)=(n,0)$，其中 $n\ge0$。在全部分离语境中，两项最小值如下，而且每一行的两个最小值由同一个语境同时达到：

$$
\begin{array}{c|c|c|c}
\text{终端观察}&\text{深度范围}&\min b(C)&\min\mu(C)\\\hline
o_2&n\ge1&2&F_{n+2}\\
o_2&n=0&2&2\\
o_m,\ m\ge3&n\ge1&1&F_n\\
o_m,\ m\ge3&n=0&1&1
\end{array}
\tag{NIC.27}
$$

下界允许任意多后续配对、任意实际常数以及任意位置、任意次数的一元替换。

证明配对数及非奇偶材料下界。无配对不能分离相同深度。定理9.1使奇偶分离至少需要两次配对。若 $n\ge1$，(NIC.26) 第一类首次常数有 $F_j$ 叶，第二类有 $F_{j+2}$ 叶；$j\ge n$ 与 (NIC.22) 给任何分离语境 $\mu(C)\ge F_n$。$n=0$ 时至少一次配对插入非空常数，故 $\mu(C)\ge1$。这些下界不以恰一次配对为前提。

证明奇偶材料下界。先设 $n\ge1$。若首次配对属于 (NIC.26) 第二类，仅该常数已花费 $F_{j+2}\ge F_{n+2}$ 叶。若属于第一类，首次常数花费 $F_j$ 叶，所得坐标为 $(j+1,1),(j-1,0)$。奇偶尚未分离，故分离语境必须存在第二次配对。两次配对之间若作 $r\ge0$ 次替换，则第二次配对前的坐标为

$$
(j+1+r,1),\qquad(j-1+r,0).
\tag{NIC.28}
$$

设第二个常数深度为 $q$。若 $q<j+r$，因深度为整数，$q\le j-1+r$。无论常数在左还是在右，射线输入都不能作例外配对：孔在左所需常数深度是 $j+r$，孔在右所需常数深度是 $j+2+r$。于是两个输入都得到 $(q,0)$，此后永久合并，不能分离。因此任何分离语境必须有 $q\ge j+r$；(NIC.22) 给第二常数至少 $F_{j+r+1}$ 叶，故

$$
\mu(C)\ge F_j+F_{j+r+1}
\ge F_n+F_{n+1}=F_{n+2}.
\tag{NIC.29}
$$

后续常数只增加非负材料。$n=0$ 时，所需至少两次配对各插入一棵非空树，所以 $\mu(C)\ge2$。

证明同时达到。对 $n\ge1$，取两个实际语境

$$
E_n[z]=(z,T_{n-1}),\qquad
C_n[z]=(T_n,E_n[z]).
\tag{NIC.30}
$$

在 $s,t$ 上，(NIC.21) 给

$$
\begin{aligned}
Q(E_n[s])&=(n+1,1),&Q(E_n[t])&=(n-1,0),\\
Q(C_n[s])&=(n,0),&Q(C_n[t])&=(n-1,0).
\end{aligned}
\tag{NIC.31}
$$

第一行深度差二，对所有 $m\ge3$ 分离；$E_n$ 的配对数一、材料 $\ell(T_{n-1})=F_n$。第二行深度差一，特别分离奇偶；$C_n$ 的配对数二、材料 $F_{n+1}+F_n=F_{n+2}$。

在 $n=0$ 时取

$$
E_0[z]=(\beta,z),\qquad C_0[z]=(\beta,(\beta,z)).
$$

前者在 $s,t$ 上给坐标 $(2,1),(0,0)$，后者给 $(1,0),(0,0)$。它们分别有一、二次配对及一、二片插入叶，给 (NIC.27) 的两个零深度达到。两处 $\beta$ 是两个实际叶出现。全部构造保持原括号及左右次序，不使用共享或重结合。$\square$

## 10. 同余非射线深度的精确材料阈值

**定理 10.1（首次配对强制的常数深度与叶数）。** 固定 $m\ge2$。设实际来源 $s,t$ 满足

$$
Q(s)=(a,0),\qquad Q(t)=(d,0),\qquad
a<d,\qquad a\equiv d\pmod m.
\tag{NIC.32}
$$

在全部分离语境中，三个分别最小的资源坐标恰为

$$
\min b(C)=1,\qquad
\min M(C)=a+1,\qquad
\min\mu(C)=F_{a+2}.
\tag{NIC.33}
$$

三项由同一个实际语境达到。等价地，对整数预算 $K,H,L\ge0$，存在同时满足 $b(C)\le K,M(C)\le H,\mu(C)\le L$ 的分离语境，当且仅当

$$
K\ge1,\qquad H\ge a+1,\qquad L\ge F_{a+2}.
\tag{NIC.34}
$$

证明下界。非射线标志在 $\rho$ 下保持零，任何与它配对的结果也为零。无配对时，两深度只加相同整数，同余仍成立，不能分离。

首次配对前若经过 $v\ge0$ 次替换，两坐标为 $(a+v,0),(d+v,0)$。设首次常数 $c$ 的深度为 $q$。若 $q\le a+v$，(NIC.21) 在任一左右位置均把两个输入送往 $(q,0)$。以后任意嵌套操作保持坐标相同。故分离必须有

$$
q\ge a+v+1\ge a+1.
$$

于是 $M(C)\ge a+1$；(NIC.22) 使该次常数至少有 $F_{q+1}\ge F_{a+2}$ 叶，故 $\mu(C)\ge F_{a+2}$。这处理了任意深的语境及所有后续常数。

证明达到。取

$$
G_a[z]=(z,T_{a+1}).
\tag{NIC.35}
$$

两个孔输入的标志零排除例外配对，故输出坐标分别为 $(a,0),(a+1,0)$，因为 $d\ge a+1$。相邻深度在任意 $m\ge2$ 下余数不同。唯一常数深度 $a+1$，有 $F_{a+2}$ 叶；因此 $G_a$ 同时达到 (NIC.33)。逐项必要性及这个共同达到证明 (NIC.34)，没有将不同语境的边缘最优值拼合。$\square$

## 11. 材料定理所支持的余数测试层级

**推论 11.1（零、一次、二次配对的完整区别）。** 对全部实际来源 $s,t$ 与 $m\ge2$，定义8.3满足

$$
\begin{aligned}
s\sim_{m,0}t
&\Longleftrightarrow \nu(s)\equiv\nu(t)\pmod m,\\
s\sim_{2,1}t
&\Longleftrightarrow \nu(s)=\nu(t),\\
s\sim_{m,1}t\quad(m\ge3)
&\Longleftrightarrow Q(s)=Q(t),\\
s\sim_{m,k}t\quad(k\ge2)
&\Longleftrightarrow Q(s)=Q(t),\\
s\sim_{m,\infty}t
&\Longleftrightarrow Q(s)=Q(t).
\end{aligned}
\tag{NIC.36}
$$

证明。零配对语境恰为 $\rho^v\square$，深度加共同整数，第一式成立。相同 $Q$ 在全部语境中保持相同，是 [JM 定理50.2][JM] 的已有稳定性，不需新的同余证明。

若 $\nu(s)=a<d=\nu(t)$，取已有分离常数所给语境 $H_a[z]=(T_{a+1},z)$。深度较大的输入不满足例外条件，输出深度 $a+1$。深度较小的输入标志一时输出深度 $a+2$，标志零时输出深度 $a$。两种情况与 $a+1$ 均相差一，所以一次配对对所有 $m\ge2$ 区分不同深度，无须对输入标志作许诺。

相同深度而相反标志时，定理9.1证明全部至多一次配对的奇偶测试都相同；定理9.2的 $E_n$ 对所有 $m\ge3$ 用一次配对分离，$C_n$ 对所有 $m\ge2$ 用二次配对分离，包括 $n=0$。这给其余各式。$\square$

本推论只识别这个来源与余数读数下的测试关系。单孔测试给最大相容同余的通用机制，沿用 [StrictOneHoleContexts.contextual_equivalence_is_greatest][SOHC] 及 [上下文几何 §§1–3][CG]；准确深度观察的 $Q$ 商沿用 [JM §50][JM]。这里的承重增量是 (NIC.27)、(NIC.33) 的全语境下界和实际共同达到，而非另立通用商定理。

**命题 11.2（零深度的奇偶边界与模数条件）。** 取实际来源 $s=\alpha,t=(\alpha,\alpha)$。其坐标分别为 $(0,1),(0,0)$，任何至多一次配对的语境都不能以奇偶区分，$C_0[z]=(\beta,(\beta,z))$ 则以深度一与零区分，并达到两叶材料下界。另取 $u=(\alpha,\alpha),w=\rho^2u$，它们的坐标为 $(0,0),(2,0)$；$G_0[z]=(z,\beta)$ 以深度零与一区分，达到常数深度一、材料一的阈值。若改取 $m=1$，任何来源和任何语境的终端余数皆为零，以上分离结论不成立。

证明。$(\alpha,\alpha)$ 不满足 (NIC.21) 的例外条件，故坐标 $(0,0)$；迭代更新给 $Q(w)=(2,0)$。定理9.1、9.2与10.1给所述下界与达到；模一的余数恒为零。$\square$

## 12. 语义、取得、历史与归属边界

**定义 12.1（实际执行的附加合同）。** (NIC.23) 规定数学来源间的代入测试。若把一次测试解释为实际取得，另须供应绑定同一来源及纪元的合法有序拼接和前向替换操作、每个常数的真实取得或准备、终端余数的真实读出以及消费者可访问的实际历史。取得次序、常数准备、替换、拼接、记录保持、访问、本地计算与输出分别计价。仅有假设1.3的 $\mathrm{Read}(q)$ 口时，允许动作仍只有原地址读取、声明的本地计算与普通停止；(NIC.23) 的数学语法没有增加操作权限。

定理9.2与10.1优化的是给定比较来源后的静态语境。达到常数依赖 $n$ 或 $a$，因此这些量词不是一个仅依据未知来源的已取得历史选择常数的共同策略。两个孔路径配对不能给有限常数菜单、控制状态、地址长度、总查询数、峰值存储或持续时间的界。$\mu$ 不计共享描述的长度，也不计外层 $\rho$ 后的展开材料；$M$ 是常数的内在解生成深度，不是其树高。若实际合同按另一资源计价，须证明对应的资源运输。

**约定 12.2（当前投影与真实入口域）。** 本节测试的自变量是当前树，不是 [JM 定义37.1][JM] 的联合入口输入 $(x,k,y)$。其当前树 $\beta$ 的既有不可区分输入 $(\alpha,1,\beta)$、$(\beta,0,\beta)$，对每个共同语境都代入同一树，对每个共同当前地址也给同一回复，入口和次数却不同。这里直接沿用 [JM 定理37.3][JM]：取得当前 $Q$ 或全部当前投影测试值，不补回被擦去的真实入口选择。

**约定 12.3（数学引用与适用范围）。** (NIC.27)、(NIC.33) 及其匹配构造为 repo-derived 普通数学推导。坐标与全部叶的例外配对供应由 [IntrinsicSubstitutionCoordinates][ISC] 及其[对应 Blueprint][ISCB]给出；唯一原始射线、Fibonacci 叶数、准确深度语境商分别归 [JM §§36、37.4、49–50][JM]。字面无替换语境的孔外材料归 [ActualLeafHistoryRigidity][ALHR]；本节只按 (NIC.24) 扩展这一资源，区别插入时材料与最终展开材料。

单孔项代入与树同余的成熟背景属 literature-attested，引用 Dexter Kozen, *On the Myhill–Nerode Theorem for Trees*，作者[原文][Kozen]第2–3页的 ranked ground terms 与第3–5页的单变量一次出现代入和同余论证。第1–2页将此背景追溯至 Brainerd、Eilenberg–Wright、Arbib–Give'on；不把通用树同余归为本节的新结果。其有限 ranked 项语法可用两个零元符号、一个二元配对符号和一个一元符号表述 (NIC.23)，但本节的一元符号解释为既有 $\rho$，不是原树上的新自由构造。余数值观察可逐余数取原像语言后使用同一代入框架。该背景不提供 (NIC.26) 的来源特定例外、插入叶数最优值或原地址取得费用。本节不作外部优先权或穷尽文献缺失的断言。

[已取得行的深度恢复 §§3–7][RDR]、[已保留字面根深度 §§3–5][LRD]及[已取得内在深度校准 §§5–8][IDC]处理完整取得行、后继原地址或未知前向滞后合同；本节 (NIC.23) 不替换这些任务和资源。[Native Ambient Contact Decision 定义1.2与定理6.1][NAC]在其整个有限覆盖来源类上供应联合接触分类，[NativeCompletionSupportClosure.support_closure_iff][NSC]供应完整同时 signed support；本节不重开其已解决范围。[KBONACCI Acquisition Resources §§96–101][KAR]的指定四振幅律区域与[FIB Fiber Calculus Continuation V 定理59.3][FCV]的指定热曲线精度转移也属于不同观察合同。它们不供应本节的余数语境材料价格，本节也不取得它们的 native 实现桥。

[Nonlinear Recut Memory 定义1.1–1.2及7.3][NRM]的来源是固定长度关系与已声明的 echo、deletion、recut 动作，其 native 来源对应另列为桥接条件。保持这种来源与操作区别，不能将其中的前驱上下文或保留宽度换成本节的原树配对权限。以上归属划分保留共同来源、真实历史、观察和费用的各自变量。

[NativeRotationDepthGap.native_rotation_depth_gap][NRG]供应实际单次局部旋转的深度差、整个 Fibonacci 叶词与几何纤维的深度极值以及共同前向迭代；(NIC.23) 的孔外构造保留括号，不包含旋转动作。[NativeRankedEqualityCompiler.ranked_equality_compilation 与 support_compilation][NREC]供应固定有限残余下的精确 scalar 等式及整份负条件的可行秩支持。它们的来源范围和供应结论继续使用，但不将其原生等式判定或旋转距离换成 (NIC.27)、(NIC.33) 的语境材料最优值。

[ISC]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[ISCB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[ALHR]: ../../../D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.lean
[SOHC]: ../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean
[CG]: RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md
[RDR]: RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_ROW_DEPTH_RECOVERY.md
[LRD]: RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md
[IDC]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md
[NAC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_AMBIENT_CONTACT_DECISION.md
[NSC]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionSupportClosure.lean
[KAR]: KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md
[FCV]: FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_V.md
[NRM]: https://github.com/the-omega-institute/trureturing/blob/176edc1f6ea512f5ba55a86ba2e40ae50e7c0364/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NONLINEAR_RECUT_MEMORY.md
[NRG]: https://github.com/the-omega-institute/trureturing/blob/fbd824520b6ad2885dc25fe88387899f88078e8f/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.lean
[NREC]: https://github.com/the-omega-institute/trureturing/blob/fbd824520b6ad2885dc25fe88387899f88078e8f/D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.lean

## 追加锚（本行以下为增补区）
