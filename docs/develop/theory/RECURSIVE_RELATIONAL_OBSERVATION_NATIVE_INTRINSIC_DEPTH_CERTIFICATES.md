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
