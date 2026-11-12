# 递归关系观察：实际原子供应、候选依赖替换与原返回的有限接合

## 1. 来源、合同与所构造的安装

**定义 1.1（所用来源及记号）。** 本卷使用下列数学来源，缩写只在本卷内使用。

| 缩写 | 来源与实际使用的条目 |
| --- | --- |
| AA | [生成签名与同档案任务取得](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)，定义17.1、17.3、19.1，定理17.2、19.2，假设20.1、定义20.2、定理20.3：局部源、真实历史、分配与固定根服务 |
| CAP | [Native容量一致性与增长](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md)，定义2.2–2.4、3.1–3.4、4.1–4.6、6.1–6.3、7.1，引理3.5、4.3、6.1b、6.7：实际工作字、寻址、描述符、原行、通道与费用 |
| ARC | [行动者局部保留恢复](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md)，定义2.1–2.3、3.1、16.2、26.2、27.1–27.2，命题3.2、定理27.3：有限字库、保护头、取得、测量导出与原调用返回 |
| RCA | [Native回顾切口取得](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md)，定义11.1–11.3、12.1、命题11.4：有限字程序的双库展开及列表运算 |
| RG | [可重入守卫取得与原消费者](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md)，定义1.2、2.1–3.2、5.1、6.1–6.2、7.1、8.1，引理3.3、6.3、定理7.2、8.2：真实启动、独立守卫、完整返回及回应依赖的下一构造 |
| TMC | [运输、任务记忆与完成化](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)，§57，定义PR57.D1–D5、D7，引理PR57.L1–L4、定理PR57.T1–T2：有限原语、实际门记录、完整解析器与原修改语义 |
| LAB | [LAB算术增长](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md)，定义1.1、4.1–4.2：源操作与辅助工作分离，完整内层回复的消费 |

记有序树为 $t::=\alpha\mid\beta\mid\langle t,t\rangle$。
记 $\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$，
并使 $\rho$ 保持配对。沿用 RG 的树映射 $E(t)=\rho^2(t)$；
它与原 ReadE 的代数值不是同一个对象。
写 $n(t)$ 为逻辑叶数，$a(t),b(t)$ 为两种逻辑叶数，
$w(t)=2a(t)+3b(t)=n(E(t))$。设

$$
D=\langle\beta,\alpha\rangle,\qquad
B=\langle D,\beta\rangle=E(\beta),\qquad
C_0=\langle B,D\rangle=E(D).
$$

树 $C_0$ 与 RG 消费阶段 $C_0$ 用上下文区分；下文把前者简称为树 $C$。
它的实际前序令牌为 PAIR、PAIR、PAIR、beta、alpha、beta、PAIR、beta、alpha。
源的物质 unary 标记不算逻辑叶。

**假设 1.2（基础转移与完成条件）。** Native 一侧采用 TMC PR57.D1
的顺序原子转移，CAP 的当前所有权、十二工作字、描述符、寻址及闭合栅栏合同，
ARC/RCA 的有限字库与测量导出，RG 的原始 beta 准备、种子取得、调用及返回合同。
AA 一侧采用 AA20.1 的真实分配、实际引用、当前独占源及记录权限、逐域读写、
比特输入输出和局部完成条件。每个声称完成的有限执行有其实际所需的有限新材料和工作空间；
没有并发写者、撤权、崩溃或中断。

新增固定连接是忠实的单比特连接：空时只有绑定的发送者能 OUT；
接收者 IN 消费该实际比特，完成规定的 backing 写入后才允许下一次 OUT。
满／空、端点及子阶段都有真实有限状态。完整声明输入在对应 IN 处供应；
不预置尚未到达的输入。原控制器、先验及字运算只使用其实际到达的有限计算。
这些条件不含候选库、生成代码、释放回应、返回状态或成功结算的存在。

**定义 1.3（单一增广安装 $J$）。** $J$ 的名称为
`JCOMP1-A1T1`。保持 RG 的0–73端口及其所有者，增加行动者 $A$ 的74，
生产者 $P$ 的75、76、77。74先保存 companion，随后追加结算ACK；
75保存请求及输出，76保存已收元数据，77保存字段快照和激活上下文。
16仍是 $P$ 的私有源／工作 arena，17是其描述符，21是完整公有暂存块，
22先存本次 Input22，随后是另测起点的原生表达／栈记录。
行动者描述符仍在29，字库仍在64–68；70仍归行动者。
25、27、16、17的令牌均不加入工作字借用。

工作字始终只有实际端口1–12。每次借用有十二个 TOK 和一个阶段CTL；
部分借用期间不运行辅助过程。所有新过程按有限调用点内联，具有固定返回边；
运行时地址、长度、计数、父帧和引用均写在字或记录中。
有限控制只选择固定端口、字段号、运算符、字库奇偶及协议阶段。

AA 有两个不同的实际分配根 $O,F$，各绑定一份 AA20.2 固定根驱动器，
各有其源、父子域、header、路由带及当前权限。
另有一个 supervisor，拥有请求／回复 backing、路径栈、重放链接、outbox、
尝试记录、当前上下文槽和结算记录流。根槽不重绑定。
选择上下文只在两个已装连接间选择，不是任意引用调用原语。

五条新增有向连接依次为 $P$ 请求到 supervisor、supervisor 回复到 $P$、
$P$ payloadACK 到 supervisor、$A$ 结算到 supervisor、supervisor 结算ACK到 $A$。
第二条按互斥阶段传 boot-done、RequestACK、Response、Confirmation。
两个 AA 驱动器各保留自己的内层请求／回复连接、End、局部ACK和同根Return。
这些连接与原48／49通道不是同一种通信动作。

**定义 1.4（字、类型与真实身份）。** 写

$$
U(k)=1^k0,\qquad D(x)=x\mathsf{sep},\qquad
B(x)=U(|x|)x,\qquad
T_r(x_1,\ldots,x_r)=\prod_{i=1}^r B(x_i).
$$

$D$ 用于原生混合符号流；$B,T_r$ 的载荷只有比特。
不得用 sep 扫描器解析相邻的 $B$ 域。
所有原类型编码保留。若旧有限类型表的最大长度为 $m_0$，
新类型按下列有限顺序编号 $i\ge1$，其字为 $1^{m_0+1}0U(i)$：
joint-description、joint-identity、N1-bank、N1-input22、N1-input-handle、
N1-field-01到28、N1-companion及其local-ref、N1-call-local-ref、
N1-z、N1-T、N1-d、N1-M、N1-N、N1-C、N1-L、N1-W、N1-Attempt6、N1-Q及N1-Q-ref、
N1-requestACK、N1-response-parts、N1-payloadACK、N1-confirmation、
N1-delivery-association、prepared-q-plus、prepared-g-plus、prepared-j-plus、prepared-m-plus、
rb22-start、rb22-FEND、rb22-next-ordinal、rb-record-field-1到7、
rb-code-base、rb-code-length、rb-circuit-bit、rb-generated-code、rb-installed-identity、
current-response-ref、NSPROV2、NSSETWAIT2、NSSET2、NSSETDONE2、
NSACKLEN2、NSACKBODY2、NSACKEND2、NS74-head、builder-base、builder-length、boot-done，
随后是定义2.4中 P00–P28 按行号及语义字段号递增的 pack-field 类型，
最后是 rb-active-frame、rb-active-node、rb-wait-frame、rb-next-node、
rb-return-result、rb-return-parent、rb-return-slot、rb-dummy-reference、rb-dummy-zero、rb-fault、joint-builder-fault。
未使用的 builder-base/length 只是保留名，不承载活跃写入。
长度规则使所有新字与旧字不同，且不同 $i$ 的新字不同。

将本卷有限日程和所引用的原过程按 CAP2.3 的过程序、文字出现序展开，
Native 行编码为 $U(q)U(op)U(i)U(j)U(s)U(q_0)U(q_1)$。
AA 行采用同一文字序，操作码为分配、null／引用／比特测试、逐域读写、IN、OUT、
局部ACK及阶段转移的有限编号；行的操作数是固定槽名或固定常量，引用值留在实际槽中。
设所得 resident 行表为 $R_N,R_A$，注册表为 $\mathcal R$。
外层逐字面安装边写入这些行和

$$
\mathscr D=T_4(\mathtt{JCOMP1\!\text{-}\!A1T1},
                 \operatorname{enc}(R_N),\operatorname{enc}(R_A),\mathcal R).
$$

该描述写在21并有真实17描述符；取得其完整本地引用 $d_P$ 后再写

$$
I=T_4(\mathtt{RBG1},d_P,d_P,\mathtt{1100100000010}),
$$

取得 $i_P$。文字常量是固定ASCII八位组的最高位先行比特；
RBG1为 `01010010010000100100011100110001`。
resident 行中不含 $\mathscr D,I$ 的未来描述符数值或自身描述的字面内容。
实际外层安装边不属于被其安装的 resident 表。
按 CAP6.3 的真实通道复制 $\mathscr D,I$ 到行动者；其本地引用不同，
origin 分别为 $d_P,i_P$。Q使用 $d_P$，Input22使用 $T_2(d_P,i_P)$，
新行、sidecar、结算及ACK使用实际取得的同一 $I$ 载荷。

**命题 1.5（安装的良基性及身份边界）。** 定义1.3–1.4给出有限安装，
不需要自包含描述、未来地址或把两个来源认作同一个源。

**证明。** 过程名、类型、端口、字段号和字库寄存器的联合是有限集合。
变量循环是带实际头和终止测试的有限行回边，固定调用图从原语到字运算、
描述符、取得、生成、行与返回，具有有限展开深度。
AA 路径、重放索引及栈引用不进入行号集合。
先有 $R_N,R_A,\mathcal R$，再有外层写出的 $\mathscr D$ 及其描述符，
再有 $I$。后续Q、DA、Input22、结果、行、sidecar、结算、ACK按此顺序依赖更早完成对象。
没有对象引用自己的未来描述符。
CAP6.3给出实际复制和相同载荷，不把行动者本地引用改成生产者引用。
AA 的两个分配根与 Native 准备发生在不同分配关系内；
以后完整令牌字相等只建立内容对应。$\square$

## 2. 完整字段、目标写入与保存不变量

**定义 2.1（直接块写入 Raw）。** Raw 的入口为：实际完整字在工作端口1，
其余以后需要的值已有完整记录；$P$ 拥有全部十二字。
目标 $t$ 是21、22、75、76、77的一个固定分支，描述符端口是17。
其顺序为：

1. Base$(t;2)$ 测实际基址 $U(b)$；该值只留在工作字2。
2. Last1，从完整输入作干扫描，在3构造实际 $U(\ell)$。
3. Last1、Tail$(t)$、FieldBody$(1,t)$，追加 sep、status0；释放输入1。
4. 用不同输出的 Add 依次构造 $b+\ell$、$b+\ell+1$。
   固定CTL置换把完整十域放在十个不同角色：
   owner、port、base、length、creation、type、initialized、mutable、status、origin。
   initialized为1，mutable为0，origin为空；creation角色与另外两角色完成实际旧描述符计数和加一。
5. 十域齐备后才 Tail17、WriteDescriptor。描述符 seal 后 At$(t;b+\ell+1)$、WR1、CTL可用。
6. 复用已死角色，用11作输出、12作长度临时字，按 CAP6.1 八域次序构造真实引用，
   Copy到实际端口1，恢复恒等角色，付费 Tail$(t)$、Tail17后返回。

Raw 内不调用 Raw 或字段快照写入；特别是目标77时也不在77暂存自己的基址或长度。
所有 Last、At、Add、字复制、角色CTL、状态写和计数均是 CAP 的实际展开。

**定义 2.2（复合字的准备与装配）。** 每个静态族 $\sigma$ 的每个字段 $j$
有其独占类型 pack-field-$\sigma$-$j$。先完成所有嵌套子字，
完整取得第 $j$ 字段后 Raw77 保存；任何源解析都先消耗完整界限并检查结束，才保存选择字段。
同一族在一次装配结束前没有递归调用或覆盖其快照的边。

所有字段完成后 New11。Reload 只使用1–10，保存11、12的字节及头；
它逐域完整扫描17，检查全部引用／类型／flags／seal／status，
再按实际长度复制所选快照到1。对每域执行 Frame$(1,11;12)$。
Reload的固定角色如下；关闭前缀及字段扫描均使用同一分配。

| 实际角色 | 活跃内容 |
| --- | --- |
| 1 | 选择域的完整输出字 |
| 2、3 | 请求ordinal、当前扫描ordinal |
| 4、5 | 计数加一输出临时字、字面 $U(1)$ |
| 6 | 本次静态期望type／tag |
| 7、8、9 | 已选实际base、length、status |
| 10 | 当前完整描述符域／检查临时字 |

计数加一后交换3／4的角色；逐域重扫只覆盖10。
完整status地址计算及比较完成后释放已死的ordinal／type／检查字，
再用这些角色执行At及有界载荷复制。期间没有任何11／12操作、描述符追加或快照写入。
原始线帧则用其规定的 Frame、FieldBody及字面位追加，不额外包成元组。
活跃11前缀期间只允许这些保存11的 Reload、Frame、FieldBody和字面追加。
Finish11、Copy11到1后，全部源游标及前缀临时值已死，才执行 Raw目标。
在 Base目标与它自己的 payload／sep／status 完成之间没有其他目标追加。

**引理 2.3（实际写入及十二字界限）。** 定义2.1–2.2在任意有限既有目标和描述符前缀上，
写出其字段所决定的完整字、实际基址、长度、status和引用；不选择交错写入形成的错误区间，
不需要第十三个工作字。

**证明。** Raw 的 Base完成后，目标只有其自己的字段复制会延伸。
长度扫描不改目标；FieldBody在第 $r$ 步后已写恰好输入前 $r$ 位，
故 payload是 $[b,b+\ell)$，sep在 $b+\ell$，status在下一格。
基址2和长度3在这个复制结束前不被辅助写入重用；之后输入及临时和已死，
能置换成十个完整描述符域。creation计数只跳过已封存域，
使用creation自身及11、12，恰好在十二角色内。
状态地址的两个加法输出均不同于输入。构造八域引用时flags／origin角色已死，
可供字面descriptor-port等临时字段使用。

Reload由每次完整单域扫描重载，扫描期间不写17，载荷复制不写11、12。
Frame的输入1、输出11和长度12不同，完成时11在R。
因此对字段数归纳，11就是已完成域的 $B$ 拼接。
所有子字和快照写入早于最终Base，允许子字与父字同在77或21，
却没有同目标活跃源游标。描述符与status指向同一已测区间。
单域选择在全解析结束后保存，故保存不会破坏待用预算或解析头。
每个扫描有固定有限旧界限，CAP3.5、6.1b给出终止。
失败测试进入保留的 joint-builder-fault，没有正常返回或源拒绝标签。$\square$

**定义 2.4（生产者复合字的完整目标表）。** 下表中 $T_r$ 的各语义字段
各有定义2.2的快照类型；单字原样阶段直接用Raw，不再套Frame。
“实际”始终指本次执行已完成对象的载荷或完整引用。

| 族 | 目标 | 语法与来源 |
| --- | --- | --- |
| P00 | 21 | 定义1.4的 $\mathscr D=T_4$，外层安装的四个有限字 |
| P01 | 21 | 定义1.4的 $I=T_4$，P00的实际引用在先 |
| P02 | 21 | Attempt6：call-origin、companion-origin、round、guard-ref、$c$、start-fence-ref |
| P03 | 77 | $T_5$：实际旧 $h,K,r,p,v$ 的暂存引用 |
| P04 | 77 | $T_5$：实际旧 $q,g_c,e,j,m$ 的暂存引用 |
| P05 | 77 | $T_4$：预备 $q+1,g_c+1,j+1,m+1$ 的引用 |
| P06 | 77 | $T_2$(P04载荷,P05载荷) |
| P07 | 77 | $T_2$(旧semantic-end option,旧unified-end option) |
| P08 | 77 | $T_6(U(d),U(M),U(N),U(C),U(L),U(W))$ |
| P09–P11 | 77 | 各 $T_2$(实际guard／proposal／waiting原引用,完整取得副本的引用) |
| P12 | 77 | $T_4(\xi,boot,prior,seed)$，保留各原绑定的完整字 |
| P13 | 77 | $T_2(d_P,i_P)$ |
| P14 | 77 | $T_5$(原caller-kind,$c$,ComputedReturned,`RBC1LEFT-A1T1`,ServiceReleased) |
| P15 | 77 | $T_5$(call-origin,guard-origin,proposal-origin,round,previous-selected-final-origin) |
| P16 | 75 | 定义3.4的Q20；其真实引用另以N1-Q-ref保存 |
| P17 | 75 | 原始线字 $0001\,B(Q)\,010$ |
| P18 | 76 | 实收RequestACK的header、unary长度、完整echo、ending原样拼接 |
| P19 | 75 | 原始线字 $1010\,B(Q)\,U(L)\,010$ |
| P20 | 76 | 实收Confirmation的header、长度、完整echo、$U(L)$、ending原样拼接 |
| P21 | 77 | $T_6$：实收Response的header／echo-length／完整echo／C／L／ending六块引用 |
| P22 | 77 | $T_5$：实收Confirmation的header／echo-length／完整echo／L／ending五块引用 |
| P23 | 21 | DA6：NSDA2、Q-ref、P21载荷、实发PayloadACK-ref、P22载荷、1111 |
| P24 | 77 | $T_2$(P21载荷,DA-ref) |
| P25 | 77 | $T_7(q,g_c,e,j,m,semantic-end option,unified-end option)$，此处为实际旧值 |
| P26 | 77 | BANK值 $T_3(U(c_R),U(s),b)$，$c_R$真实库描述符序号、$s$真实槽计数、$b\in\{0,1\}$ |
| P27 | 22 | 定义5.3的Input22完整28域 |
| P28 | 21 | 定义8.2的NSPROV2完整15域，实际J/U引用在先 |
| P29 | 21 | 完整原始单字：28个解码域、旧／预备字段、handle、rb22-start、code-base／length、next-ordinal、七个记录字段 |
| P30 | 77 | 完整原始单字：active-frame／node、wait-frame、next-node、return-result／parent／slot、dummy-reference |

P18、P20复制已收 backing，形成真实完整帧引用；不是重新生成一个同值回复来代替接收。
旧canonical引用列表、manifest、栅栏、行、索引、计数器及48／49通道
仍按 CAP 各自完整语法和原写入合同处理，不被新固定元组的字段数替代。

**定义 2.5（行动者与AA的写入表）。** 行动者使用 ARC26.2 测量导出。
所有持久输入先放在不同字库域；在干计数／载荷复制的两个pass之间源字库版本不变，
没有字库赋值或嵌套导出。base、length、status在本次导出的本地工作字内。

| 族 | 目标 | 完整语法 |
| --- | --- | --- |
| A00 | 74／29 | 定义3.3的Companion17 |
| A01 | 25／29 | 原RG回应状态、原完成轮状态，保持RG3.1语法 |
| A02 | 字库 | pending／completed内部列表，线catalogue每项为五个B域 |
| A03 | 28／29 | Wait12：NSSETWAIT2、捕获的新返回状态-ref、原waiting-packet-ref、实收sidecar-local-ref、$c$、旧CountsEnds7、新CountsEnds7、SourceBindings4、GuardBinding2、ProposalBinding2、round、$I$ |
| A04 | 28／29 | 定义9.1的M：九B域、$U(d)$、$d$个五B域项 |
| A05 | 74／29 | 实收ACK长度字，自己的sep／status／描述符 |
| A06 | 74／29 | 恰好实际ACK长度的body，ending完成前status0 |
| A07 | 74／29 | 实收三个ending位，另有sep／status／描述符 |
| A08 | 28／29 | Done8：NSSETDONE2、wait-ref、M-ref、ACK-length/body/ending三引用、捕获的新返回状态-ref、实查choice |

线上的 $B$ 拼接由实际 Length、cons、Cat、Reverse生成；
它与RCA内部的计数／终止列表语法分开。
AA 的对应构造均为真实辅助对象：新header、逐位分配并先写bit和next=null，
再接前tail.next或head，最后更新tail。接收锁存器在这些写入前不清除。
RequestACK、Response-header、transportACK、Confirmation、settlement-body、
九个解析域、catalogue、binding、settlementACK、length-marks和各cursor／budget
占不同固定槽。输出前完整干遍历实际列表并封存。
AA不使用Native描述符数值作分配引用。

**引理 2.6（行动者保存及74复用）。** A00、A03–A08不改变原25／27的旧载荷，
结算ACK追加不破坏A00的companion；捕获的新返回状态在结算后仍可重载。

**证明。** ARC的赋值只写64–68的新版本；导出在固定25／28／74上测量尾部，
其源字库在两个pass间不变，十域描述符和可用状态在载荷后。
所有捕获handle、两个闭合描述符界限、$I,M$、等待绑定及保存的74头
是不同字库域。74的每一后继基址不小于前块的base+length+2。
其companion的原区间、sep、status和29描述符不再写。
ACK入口用ARC3.1固定74分支保存头到L的实际距离及是否R：
普通格／L在结算后按距离恢复，原R约定恢复为扩展后的Tail74。
不声称旧R格扩展后仍是R。读取companion使用它自己的精确描述符和预算，
不使用Last74。捕获状态按完整引用重载，不采用较旧LatestType匹配。
故追加与工作字重用均不能把原快照装回当前源或抹掉本次新回应。$\square$

## 3. 从真实启动到已绑定的原C1调用

**定义 3.1（联合启动的固定日程）。** 安装并实际复制定义1.4的描述及身份后，
AA分配两个alpha根，初始化各自parent／left／right／header为null，
将返回的实际引用写入各自固定驱动器根槽。
在 $O$ 上依次执行

$$
P_\varepsilon,\ S_\varepsilon,\ S_L,\ P_R,\ S_{LL},\ P_{LR},\ S_R.
\tag{AS.1}
$$

每项都是完整AA20.2请求、真实Growth、End、局部ACK、同根Return；
supervisor先保留完整回复副本才ACK。$F$无编辑。
七项完成后才输出boot-done字0010；$P$在76 backing并完整检查它，
才进入RG2.2的原Native初始化及实际内部mode10。
随后原Lift依次完整返回Reserve3、Raise3、Rho、Rho。
原内部阶段 $C_0$ 构造Rho，独立实际接收 $U(2)$，
按原Plan执行Reserve5、Raise5、最终Rho，各走完整原行／ACK／返回。
其后原Entry、loan、reload、Select才构造阶段 $C_1$ 的Left操作数。

本卷两条声明路径在此分别实际接收新的 $U(2)$ 或 $U(4)$。
前者不维护；后者完整执行Reserve10、Raise10及各自返回，
然后到达最终Left的原ComputedWait。下一阶段的守卫不在输入中。

**引理 3.2（实际达到的共同内容关系）。** 定义3.1的同一安装，
在两条声明路径的最终Left等待点有：
Native当前实际源为 $C$，实际原encoded Left操作数也为 $C$；
$O$实际内容为 $C$且Ready，$F$仍是实际alpha且Ready。
这些关系由实际历史建立，不是入口fixture。

**证明。** (AS.1)的逐步逻辑目标及结果如下；每个分裂目标为beta，
每个提升目标为alpha。

| 已完成事件 | 该时刻整个 $O$ 的内容 |
| --- | --- |
| $P_\varepsilon$ | $\beta$ |
| $S_\varepsilon$ | $D$ |
| $S_L$ | $\langle D,\alpha\rangle$ |
| $P_R$ | $B$ |
| $S_{LL}$ | $\langle\langle D,\alpha\rangle,\beta\rangle$ |
| $P_{LR}$ | $\langle B,\beta\rangle$ |
| $S_R$ | $\langle B,D\rangle=C$ |

AA20.3供应各实际Return，Maintain建立其真实路由带。
Native初始化有自己唯一的beta IN准备与种子取得。
RG7.2的四次Lift给出 $E(\beta)=B$，其原来源及地址不变。
实际 $C_0$ 的参考候选是 $D$，两叶在独立guard2处接受；
原维护及Rho返回给出实际encoded源 $E(D)=C$。
RG8.1的后继Select复制刚取得的参考后继 $D$，
原两次替换转换生成encoded操作数 $E(D)=C$。
这不是将AA源名用作Native输入。
U4的Reserve10只扩展实际 $\phi_K$，Raise10只提高原guard，
各保持原源内容、旧地址及保护的等待资料；U2无这两项。
所以两者的源及操作数仍为 $C$。$\square$

**定义 3.3（companion及实际调用的取得）。** 在选中的最终ComputedWait，
$A$拥有全部工作字。按RG3.2 Close29、原state重载及ARC保护头导入，
取得实际packet27、waiting25、$G_i$、guard、proposal的完整字及其引用。
用A00在74导出以下17个B域：

| 域 | 载荷 |
| --- | --- |
| 1–5 | 版本N1-COMPANION-J1；实际packet27-ref；完整packet字；实际waiting25-ref；完整waiting字 |
| 6–10 | 完整 $G_i$；实际guard-ref；完整 $U(h_i)$；实际proposal-origin；完整proposal字 |
| 11–14 | $\xi$；实际 $U(i)$；当前previous-semantic-end；当前previous-unified-end |
| 15–17 | 完整原 $k,z,c$ |

原packet语法仍是 RG 的 $T_4(\mathtt{RG\!\text{-}\!CALL2},k,z,c)$。
先用完整49通道发送companion到 $P$ 的21／17，检查并ACK，工作字返回 $A$；
再按原RG6.1发送原packet并完整检查／ACK，工作字返回 $A$；
随后才执行原十二TOK到 $P$ 的调用转交。
$P$比较packet与companion的完整origin、$k,z,c$、轮、guard、proposal、等待及两端点，
再运行CAP4.6原canonical三块构造、完整原前缀解析及转换。
guard及waiting的外来引用在 $P$ 只是绑定键；其完整取得载荷来自companion，
不成为读取25／27的能力。

**定义 3.4（唯一开始栅栏及Q20）。** 仅在原合法admission取得一次源服务令牌。
按原ReadState、LoadCounter和索引扫描取得实际旧值及两端点，
用P29分别保存旧 $h,K,r,p,v,q,g_c,e,j,m$。
用不同输出的Copy／Add$(U(1))$准备 $q+1,g_c+1,j+1,m+1$并保存。
当前BuildManifest完成后执行本次唯一CloseFence(source-start)，保留其真实六域载荷及引用。
Attempt6的六域是P02所列顺序。
Q的20个B域严格依次为：

| 域 | 载荷 |
| --- | --- |
| 1–5 | 0001；完整Attempt6；companion发送者origin；完整Companion17；原call-origin |
| 6–10 | 完整canonical request-reference word；完整原前缀 $z$；完整转换后令牌字 $T$；$U(d)$；$U(M)$ |
| 11–15 | 实际ReadState的 $U(h),U(K),U(r),U(p),U(v)$ |
| 16–18 | $U(N),U(C),U(L)$，其中 $N=2h-1,C=1+M+N,L=2C$ |
| 19–20 | 真实开始栅栏六域载荷，其引用为Attempt6第6域；$d_P$ |

canonical request-reference word保留 CAP4.6 的实际计数和header／length／payload
三个完整13引用，本语言的context已在payload中。
本次 $z$ 是实际14位原前缀，$T$ 是实际18位九令牌字；
不按这两个长度推断载荷。需要的 $G_i,z,T$ 等完整字均先Raw21保存，
其实际引用才进入后续字段。

**引理 3.5（源前态与原调用谱系的保存）。** Q、后续取得及公开生成之前的
所有旧值和预备值是这次实际原调用的值；源开始栅栏发生一次，
随后到第一个源STORE之前源、目录和旧计数不变。

**证明。** 原packet及companion都在其发送者封存后复制，CAP6.3／ARC27.3
保证收方实际字及origin，全部字借回后才作最终调用转交。
原canonical构造复制实际 $k,z$，没有匹配外部帧IN。
ReadState和计数扫描早于栅栏且持有独占源令牌；字段保存与manifest写入
只写工作字、21／17／77和实际meter。
其后的AA通信、Input22、forest和代码生成没有源目的写或目录提交。
辅助工作不会把预备计数选为当前值。
f只在实际栅栏前进，不在后续用保存的旧f覆盖。
U4的 $G_i$ previous-final仍是 $C_0$ 最终行；其waiting的previous-unified
则已经是后来的Raise行，二者分别保存。$\square$

## 4. 实际历史重放、候选编辑与Tag供应

**定义 4.1（内层请求表与supervisor工作）。** 采用AA20.2允许的下列字面表。
请求Tag／P／S／HasPromotion／HasSplit／FetchGrowth／Next分别为000到110，111为bad；
回复Tag／Boolean／Refusal／Growth／Recall／Next／OutOfRange／BadFrame分别为000到111。
Tag载荷alpha00、beta01、branch10、absent11；Growth／Recall的kind为P0、S1，
路径L0、R1。地址 $A(p)=U(|p|)p$，索引 $U(k)$。
这些Tag位与Native令牌alpha01、beta10、PAIR11、PAD00有不同类型。

每次内层调用先写真实发送字，再逐位发送；supervisor接收全部回复和End，
将完整副本封存后才局部ACK，等待该驱动器同根Return，才运行后继。
栈节点存真实next及路径副本，Push逐域写后链接，Pop读其域后更新栈槽。
索引／长度／路径均有实际有限列表；控制只选择两个固定根连接。

**定义 4.2（旧源全字检查与历史重放）。** supervisor收到并完整解析Q后，
先在 $O$ 运行如下Tag遍历：栈初始含空路径，Pop路径 $p$，实际请求Tag$(p)$，
收到alpha／beta即追加对应Native令牌；收到branch即追加PAIR并先Push $pR$ 再Push $pL$。
absent为局部失败，不进入原源拒绝返回。
栈空后将完整遍历字与Q内实际 $T$ 比较全部位和结束。
已知种子的有限重建沿用AA命题22.2、34.2的方法，逻辑arity遍历沿用AA定义26.2；
这里每一步仍使用定义4.1的三位固定根接口，不采用AA26.2的四位handoff服务。

随后实际构造 $U(1)$，请求 $O$ 的FetchGrowth$(i)$。
收到Recall$(e,p)$，保留完整回复，按该实际kind／address在 $F$ 发送P或S，
消费其真实Growth／End／ACK／Return，追加一条封存重放链接
（实际索引、旧Recall副本引用、新Growth副本引用），才加一索引。
只有真实OutOfRange结束重放；不把七作为循环输入。

**引理 4.3（真实重放及不同事件谱系）。** 定义4.2结束时，
$F$在其原分配根上真实达到 $C$并Ready；其源、header和路由带完全由自身分配及自身事件建立。
$O$源和原路由带不变。重放链接对应内容相同的事件序列，不认同事件身份。

**证明。** Tag只依当前实际逻辑arity返回；branch恰有两个逻辑孩子，
beta的unary物质标记不入栈。有限树的每个逻辑节点访问一次，
产生其完整前序字，故检查的是实际 $C$的整个字与实际取得 $T$。

AA19.2使第 $i$ 次有效Fetch返回实际第 $i$ 个旧事件及完整地址。
归纳假设重放前 $i-1$ 项后 $F$内容为旧历史相同前缀的内容。
AA17.2使下一地址及类型合法，AA20.2的Navigate／Guard实际再检查，
Reserve取得 $F$的材料，编辑及Maintain只写 $F$的源和祖先header／cell。
因此第 $i$ 项真实可执行，完整Return后不变量恢复。
旧历史有限，首个OutOfRange终止；这里是七项后索引八。
没有 $O$ 引用写入 $F$的源边、parent、header或路由next域。
链接中的跨记录引用只在supervisor的辅助记录内。
$O$只收到查询；相同的早期侧词是不同事件投影，不是旧记录搬家。$\square$

**定义 4.4（八次候选编辑及真正outbox）。** 重放后在 $F$ 依次完整执行

$$
S_{LLL},P_{LLR},S_{LR},S_{RL},P_{RR},S_{RLL},P_{RLR},S_{RR}.
\tag{AS.2}
$$

每次都经过当前目标检查、Maintain、完整Growth／End／ACK／Return。
然后按定义4.2的Tag栈遍历 $F$，将每个实际回复转换的两位令牌追加到其真实outbox。
实际计数已输出令牌，用收到的 $C$ 容量字补PAD到恰好 $C$ 槽；
容量不足进入局部失败。全部位、长度、尝试关联写完后才封存outbox，
将其实际引用写入此Q的尝试记录，再允许Response打印。

**引理 4.5（候选内容及有限供应）。** 在定义3.1的两条路径上，
定义4.4真实得到 $\langle C,C\rangle$，其outbox是该树的十九活跃令牌，
随后补到收到的 $C$ 槽。所有循环有限，不需要Clone、Serialize或新根入口原语。

**证明。** 开始 $F=\langle B,D\rangle$。
前三项分别在左子树的LL、LR、R相对位置作用，
把左 $B=\langle D,\beta\rangle$ 变为 $C=\langle B,D\rangle$。
右子树 $D$ 上的后五项为相对 $S_L,P_R,S_{LL},P_{LR},S_R$，
也把 $D$ 变为 $C$。每个S目标是实际beta，每个P目标是实际alpha；
相应分裂先于新位置的后续事件，故不是符号上省略的编辑。
两子树编辑互不写对方的源域，但祖先路由带按真实次序都作Maintain。
结果有十叶、九branch，Tag遍历产生十九令牌。
实际容量为19或29，故分别补零个或十个PAD。
旧Tag栈访问有限九节点；重放停止于有限旧历史的OutOfRange；
编辑表有八项；新Tag栈访问有限十九节点；padding消耗已收到的有限容量字。
每个内层操作由AA20.3给出完成。
所有输出都来自逐域构造及真实Tag回复，没有复制源引用结构的隐含操作。$\square$

## 5. 忠实运输、关联记录与真实Input22

**定义 5.1（外层线语法及实际接收）。** 外层字为

$$
\begin{aligned}
\mathrm{Request}&=0001\,B(Q)\,010,\\
\mathrm{RequestACK}&=1001\,B(Q)\,010,\\
\mathrm{Response}&=1100\,B(Q)\,U(C)U(L)\,\mathrm{outbox}[L]\,010,\\
\mathrm{PayloadACK}&=1010\,B(Q)\,U(L)\,010,\\
\mathrm{Confirmation}&=1011\,B(Q)\,U(L)\,010.
\end{aligned}
$$

AA先完整backing／解析Q20并检查其固定语法、guard／call／容量绑定，
才生成RequestACK和调用定义4的供应日程。
$P$对每个接收头、unary长度、完整echo、C／L及ending分别在76真实backing。
unary接收逐位执行IN、EX、WR、RD测试、MR，通过实际0才结束；
固定长度接收用已完成的unary字：RD计数；若1则IN到5、WR目标、MR目标、MR计数；
若0才转后继。锁存器5在对应WR前不被辅助过程覆写。
echo以实测Q长度为界，比较完整字和两端，不只比较长度。

Response元数据完成后，Base16取得实际新基址 $b$，
Zero16构造 $L$ 位及sep，追加status0，写真实不可用十域描述符。
载荷循环直接把每个IN位WR到 $[b,b+L)$，不经过公开payload镜像。
完整接收、backing并检查ending010后，重载实际描述符与status地址，
才At／WR1／CTL使此不可变N1-bank可用，记其完整引用为 $r_B$、序号为 $c_R$。
其后实际发送PayloadACK；AA完整检查Q／L／ending，标记delivered，
从实收ACK生成Confirmation。$P$完成接收检查及P18／P20完整元数据归档后，
才生成P23的DA6及Input22。AA保留实际尝试／outbox，处于AwaitSettlement。

**引理 5.2（B6star：执行关系而非载荷证书）。** 在定义5.1的真实忠实串行日程中，
可用库的 $L$ 位恰等于此尝试实际封存并打印的outbox。
DA6、全部实收元数据、实发PayloadACK、完整Confirmation及AA的实际尝试／outbox
建立这一执行关联；不需要Native公开保存完整outbox的第二副本。

**证明。** 在载荷第 $t$ 步之前，AA打印游标已消费恰好outbox前 $t$ 位，
没有较早未backing的连接位，Native已写库前 $t$ 位与之相等，
头在 $b+t$，实际长度计数消耗了 $t$ 个1，status仍0。
OUT只能把当前封存outbox的下一位填入空连接；IN消费该位，
WR使用同一锁存器5，两个MR更新头和计数，backing完成再开放下次OUT。
所以前缀不变量逐位延伸到 $t=L$。
完整ending与精确描述符重载在status1之前，证明可用库恰是该outbox。
不可变flags和独占写权限保存此等式到解释、行及结算阶段。

Q含实际call、companion、guard／proposal／round、开始栅栏与continuation，
完整echo及唯一活跃supervisor阶段选择同一尝试。
AA只在实收完整PayloadACK后标记delivered，Confirmation绑定该实收动作；
DA仅引用已发生的元数据块。结算再以全字比较这些实际记录，
得到其原有outbox引用，不能换成另分配的同名对象。
证明发生在第一次候选读取前；没有从私有库事后公开读取来制造取得历史。$\square$

**定义 5.3（真实Input22的28域）。** 所有字段和嵌套子字都先按第2节完成，
再由P27在22写出一个完整比特块。其域依次为：

| 域 | 完整内容 |
| --- | --- |
| 1–4 | N1-INPUT22-J1；$r_B$；实收原call-local-ref；实收companion-local-ref |
| 5–7 | 原canonical request-reference word；实际 $z$ 暂存引用；实际 $T$ 暂存引用 |
| 8–11 | P08尺寸六元组；P03旧状态引用五元组；P06旧／预备计数引用二元组；P07两旧端点 |
| 12 | 已取得完整 $G_i$ 的本地暂存引用 |
| 13–15 | P09 guard绑定；P10 proposal绑定；P11 waiting绑定 |
| 16–18 | 完整Attempt6；实际Q-ref；实收完整RequestACK-ref |
| 19–21 | P24（完整Response元数据引用表与DA-ref）；实发PayloadACK-ref；实收完整Confirmation-ref |
| 22–24 | 实际开始栅栏-ref；实际before-manifest-ref；P12原源／boot／prior／seed绑定 |
| 25–28 | P13描述／身份引用对；P14五域return-cases；九位111110000；P15实际发生绑定 |

九位依次表示bank-ready、echo-checked、response-complete、payloadACK-sent、
confirmation-checked为1，settlement、source-write、candidate-read、candidate-parser-read为0。
flags记录已证事件，不能代替载荷／origin／状态检查。
Input22有真实17描述符和status1；以其完整引用进入ReceivedBankEntry，
工作角色恢复恒等，role1持引用，head22在该payload第一位，16在L，
0／13／17在R，其余所需值均已有完整记录。

**定义 5.4（28域实际解码与库检查）。** 先把role1真实handle Raw21保存，
结束该保存后才建立解析游标。解析其八域引用及真实十域描述符，检查
ownerP、descport17、payload22、完整ordinal／base／length／type／status、
initialized1、mutable0、空origin、status=base+length+1及实际status1。
对 $j=1,\ldots,28$ 作28个静态分支：每次重解该不可变handle，
At22(base)，建立实际全长度预算，完整运行28次ReadFrame及预算耗尽／物理sep检查，
只保留第 $j$ 字在11；整次解析结束后才Copy到1、Raw21保存N1-field-$j$。
嵌套固定元组也按同样“完整重解析后保存”的规则取域。

依第3节的全字、引用及实际等待／guard／proposal／round绑定检查全部域，
特别检查第10域的五旧／四预备引用、第19域的元数据表／DA、第25域的 $d_P,i_P$、
第26域恰五个return字段及其固定代码映射、第28域的实际previous-final。
重载 $I$ 后检查两个描述引用确为 $d_P$。
旧计数及四预备字以实际加一重新比较，before-state及manifest与Q／Attempt6／原call一致。
由实际 $h,M$ 重新构造并比较

$$
N=2h-1,\quad C=1+M+N,\quad L=2C,\quad W=3N+C+8.
$$

完整解析 $r_B$，逐域检查其真实描述符为
$(P,16,b,L,c_R,T_{bank},1,0,b+L+1,\varepsilon)$，
及其八域引用、真实status1、当前arena范围。
Base／分配不变量另保证其与全部旧源／工作区间不交。
这些步骤不读取任何候选payload位。
最后才Base22，保存新的rb22-start，追加封存
BIND$(r_B,call\text{-}local\text{-}ref,Input22\text{-}ref)$，进入BuildForest。

**引理 5.5（真实生成入口的取得）。** 定义5.4的成功入口来自第3–5节实际执行；
新的22记录区严格位于完整Input22的payload、sep及status之后。
全部解析／保存满足第2节工作字与游标条件，库检查不产生候选值。

**证明。** 第3节先供应真实原调用及旧值，第4节供应实际outbox，
引理5.2供应当前可用库及其实际描述符、ACK和Confirmation，
引理2.3供应28域的实际比特块，故解码所需每个对象都有此前实际writer。
每次全解析保留一个选择域而非28个同时活跃域；
11、预算12和固定解析临时角色在完整扫描内，Raw仅在预算结束后运行。
实际全字检查使别次同值call或伪造flags不能替代本次origin。
最后Base在所有Input22追加及解码输出之后，
故从rb22-start读取的原生tag不会把更早比特元组或旧表达识别为记录。
库地址范围和status读取是公有元数据读取；第一次候选位读取仍在后续私有解释器。$\square$

## 6. 收到的候选如何进入完整原生成器

**定义 6.1（22原生记录与选择）。** 从实际rb22-start开始，
每条记录为 $D(tag)D(w_1)\cdots D(w_a)\mathsf{seal}$。
tag为110101后接下表四位suffix，字段数和次序固定。

| suffix／种类 | 字段数 | 字段 |
| --- | --- | --- |
| 0000 E | 6 | $K,f,U(child_1),U(child_2),U(child_3),value$ |
| 0001 Q | 3 | EXPR0或STORE1、$U(node)$、$U(destination\text{ 或 }0)$ |
| 0010 F | 7 | $U(node),U(parent),slot,U(next),r_1,r_2,r_3$ |
| 0011 R | 2 | $U(node)$、完整结果W-reference |
| 0100 TOP | 1 | $U(frame\text{ 或 }0)$ |
| 0101 CUR | 1 | $U(\text{已完成Q数})$ |
| 0110 BIND | 3 | 真实bank-ref、call-local-ref、Input22-ref |
| 0111 FEND | 2 | $U(\text{实际Q数}),U(\text{冻结forest记录数})$ |
| 1000 VBIT | 3 | $U(vector),U(index),U(root)$ |
| 1001 VEND | 2 | $U(vector),U(\text{完整width})$ |
| 1010 BUILD | 6 | 固定phase、$U(slot)$、need-vector、leaf-vector、closed-root、valid-root |

Append22先从rb22-start全扫描当前完整区，按tag固定arity跨域并查seal，
真实计数加一后Raw21保存新ordinal。
逐个完整取得、Raw21保存至rb-record-field-1到7，所有字段完成才打开22目标。
Tail22、追加 $D(tag)$；每个字段由17／21重载，Tail22、WriteField；
最后EX、WR(seal)、MR，才返回已计的实际ordinal。
写入期间没有22源查找、22暂存或第二个Append22。
Lookup从rb22-start开始，真实unary计数比较目标；
一次只复制所需字段，其余SkipField，检查该seal后才选择。
多个字段作多次完整扫描。TOP／CUR取最后封存匹配记录。
Q只在FEND所冻的前缀和Q计数内枚举，后来的F／R不扩展Q集。

**定义 6.2（有限forest的构造）。** 每个基本门先为先前EXPR根追加REF叶，
再追加以这些E为孩子的运算E和EXPR Q；常量追加常量E及Q。
向量位以VBIT记录真实root，VEND证明完整的 $W$ 位数；
BUILD在整槽完成前保存旧向量和两个标量根。
循环边界全部是已完成的 $U(C),U(N),U(W)$ 或完整向量字。
其实际构造次序为：

1. 对 $s=0,\ldots,C-1$，$b=0,1$，追加BANK叶／EXPR Q，保存每个候选位根。
   BANK.value为P26实际三元组。这里没有原Left scatter或常量PAIR候选根。
2. 对每个 $i<2N$ 追加SOURCE叶／Q；保留完整原源的
   $A_s=[X_s\ne PAD]$、$L_s=A_s\land\neg A_{s+1}$ 及 $A_N=0$。
   即使这些mask不再被新候选用到，也不删其现有保留消费者。
3. 以实际 $W=3N+C+8$ 构造原完整候选parser，初值need1、closed0、leaves0、valid1。
   对每个候选槽从BANK位构造PAIR、alpha、beta、PAD测试以及

$$
\begin{aligned}
P&=[token=PAIR],\quad A=[token=alpha],\quad B=[token=beta],\\
\Lambda&=A\lor B,\quad T=P\lor\Lambda,\\
I_{bad}&=([token=PAD]\land\neg z)\lor(T\land z),\\
n_*&=n+[P]-[\Lambda],\\
n'&=\operatorname{MUX}(T\land\neg z,n_*,n),\\
\ell'&=\ell+[\Lambda\land\neg z],\\
z'&=z\lor[n'=0],\qquad v'=v\land\neg I_{bad}.
\end{aligned}
\tag{AS.3}
$$

   每槽都生成两个算术／MUX分支，包括未选臂及每个最终carry。
   全部 $C$ 槽之后构造

$$
\gamma=v\land z\land[n=0]\land[1\le\ell]\land[\ell\le h].
\tag{AS.4}
$$

4. 所有加法逐位用TMC PR57.07的五门全carry递推；
   减法逐位NOT第二操作数并以carry1进入同一加法；
   equality逐位NOT XOR后AND折叠；比较用PR57.08完整七门递推，
   有符号比较先翻转符号位。所有初始常量及复制也生成门。
   公有 $h$ 等整数的位来自真实unary字：重复倍增构造所需powers，
   由高到低Compare／Sub剩余字得到各位，再按实际VBIT索引重排到规定方向。
   不预置 $h$ 的二进制向量，不用私有叶数决定公有循环界限。
5. 对每个 $i<2N$ 构造完整EXPR根
   $\operatorname{MUX}(\gamma,candidate_i,old_i)$。
   所有这些Q先于依 $i=0,\ldots,2N-1$ 排列的STORE Q。
   FEND只在全部E／Q／向量／BUILD完成后写出其实际计数。

**定义 6.3（E的运算元数与规范字段）。** E的K及f必须满足下表，
f按输入000到111次序。$U(0)=0$ 是缺省孩子字段，
空value为真正空字，不是 $U(0)$。

| K | 运算 | f | 元数 | value |
| --- | --- | --- | --- | --- |
| 000 | CONST0 | 00000000 | 0 | 空 |
| 001 | CONST1 | 11111111 | 0 | 空 |
| 010 | COPY | 00001111 | 1 | 空 |
| 010 | NOT | 11110000 | 1 | 空 |
| 010 | XOR | 00111100 | 2 | 空 |
| 010 | AND | 00000011 | 2 | 空 |
| 010 | OR | 00111111 | 2 | 空 |
| 010 | MUX | 01010011 | 3 | 空 |
| 011 | BANK | 00001111 | 0 | $T_3(U(c_R),U(s),b)$ |
| 100 | SOURCE | 00001111 | 0 | $U(i)$ |
| 101 | REF | 00001111 | 0 | $U(\text{较早EXPR根ordinal})$ |

先实际读取完整3位K与其sep，再读恰8位f及sep；
K=010的八层有限bit trie只有表中六个叶，其他表值失败。
K的110／111、错误宽度也失败。
元数为 $a$ 时前 $a$ 个孩子均为完整正unary，
严格小于此E ordinal且选择冻结forest内已seal的E；后面的孩子全为 $U(0)$。
常量及所有变量叶的三个孩子全为 $U(0)$。
BANK值完整ReadFrame三次并耗尽，要求实际BIND匹配、$s<C$、$b$恰一位；
SOURCE要求 $i<2N$；REF要求较早EXPR Q根，不能只凭某记录号较小。
无第七个E字段；元数来自实际K／f有限分支。

**定义 6.4（活动帧、等待帧与返回日程）。** slot根为00，三个孩子为01／10／11。
根帧parent=$U(0)$；非根parent是较早封存F的正ordinal。
每个已返回 $r_s$ 是真实P16的一位、initialized1、mutable1、status1的完整W引用。
这里“已返回”表示已生成并分配该结果位置，不表示解释器已经算出其值。

| 帧状态 | next和结果字段 |
| --- | --- |
| Active | $0\le n\le a$；$r_1,\ldots,r_n$完整，后续字段为空 |
| Waiting(slot $s$) | $next=s$，前 $s-1$ 个结果完整，$r_s,\ldots,r_3$为空，$1\le s\le a$ |

初始追加CUR0、TOP0。以下都是固定边，运行时parent／slot有Raw77 backing。

| 入口 | 实际动作及后继 |
| --- | --- |
| RootSelect | 在FEND界内按CUR选下一Q；EXPR分支追加 $F(node,0,00,0,\varepsilon,\varepsilon,\varepsilon)$、seal、TOP实际ordinal，进入Drive；STORE转STORE行，计数耗尽转ForestEnd |
| Drive | 完整重载TOP及F，Raw77保存active-frame／node；检查E和Active；若 $n<a$，有限 $n=0,1,2$ 分支选孩子 $s=n+1$，进入Push；否则进入Complete |
| Push | 先追加Waiting版本并封存，保存其实际ordinal为wait-frame；保存所选child-node；追加孩子F，其parent为该Waiting ordinal，slot为本次 $s$，next0；封存、TOP孩子，回Drive |
| Complete | 只在 $n=a$ 时分配真实新三格结果块（bit0、sep、status），完整可变一位描述符后status1；保存完整result-ref；按定义6.5 Emit，追加R(node,result-ref)；从已保存active-frame重载实际parent／slot |
| RootReturn | parent0且slot00，追加TOP0，实际CUR加一，再RootSelect |
| ChildReturn | 保存return-result／parent／slot；查所选Waiting F，要求next=$s$、实际child$_s$=刚完成node且该slot空；追加只填 $r_s$ 的新父F版本，其余node／parent／slot／next／旧结果不变，TOP新父，回Drive |
| STORE | 先查引用MUX根的完整R，Emit投影到实际S(i)，不用假源结果分配；CUR加一，再RootSelect |
| ForestEnd | CUR恰FEND.Qcount且TOP0；追加唯一程序terminal0，进入CloseProgram |

每次Append22所需字段先全在21完成，活动、等待、下一node、返回结果／parent／slot
是不同77类型；没有一个活跃父信息只留在会被helper覆写的工作角色。
ChildReturn选择Waiting只能用孩子实际parent，Waiting不冒充Active运行。

**定义 6.5（真实BANK寻址及字面Emit）。** 先在16实际分配并封存一个不可变一位0块，
记其完整引用及地址为 $Z$；没有指令写它。
BANK叶重载实际 $c_R,s,b$，比较BIND完整库引用，
重做descriptor／status检查，以Copy／Add构造 $2s+b<L$，
再Add库base得到实际W地址 $b_B+2s+b$。
没有候选位RD。SOURCE给出S(i)，REF查较早根已完成R及实际结果描述符。

Emit的操作数规则为：常量 $(Z,Z,Z)$，变量叶 $(x,Z,Z)$，
一元 $(r_1,Z,Z)$，二元 $(r_1,r_2,Z)$，MUX $(r_1,r_2,r_3)$。
缺省E孩子 $U(0)$ 不会被当作地址0或dummy引用。
每次Emit的四个地址字段中，S调用实际Resolve，W复制其真实绝对unary字。
它完整写出

$$
1\,f_0\cdots f_7\,U(d)U(a)U(b)U(c).
\tag{AS.5}
$$

所有位由Append或UnaryBody写到15，三个unused字段也都存在。
STORE的目的S(i)仍调用Resolve，操作数为其真实MUX结果和两个 $Z$。
生成前Base15保存实际起点，terminal0后再次测Base、Sub得到实际长度，
追加sep／status0、真实generated-code描述符、status1及CTL，
At15实际base才是原解释器入口。未复用旧guard代码。

**引理 6.6（生成、父返回与全部原解析臂）。** 从引理5.5的实际入口，
定义6.1–6.5有限生成并封存完整字面程序。
每个E／F遵守同一运算／元数／slot规则，所有R对应已发出的真实结果位置。
程序的候选值输入全来自实际库，保留完整原parser、旧源臂和全部MUX／STORE。

**证明。** 对forest构造序归纳：每个输入叶有实际范围／引用，
每个门的REF只指向更早EXPR根，其E孩子也严格更早。
向量只在VEND的全width检查后消费，BUILD保留旧标量直到本槽所有新根完成，
所以(AS.3)使用旧值而不把部分新向量混入同一步。
PR57.07–08的全宽递推及 $W=3N+C+8$ 覆盖所需有符号范围，
包括丢弃的负一臂和最终carry，不按选择位缩短公有生成。
具体地，第 $t<C$ 槽之前 $0\le n\le t+1$、$0\le\ell\le t$：
首次到零即closed，之后不再更新need；此前减一不越过零。
所以未选中的 $n_*$ 也只在 $[-1,C+1]$ 内，叶数在 $[0,C]$ 内。
又 $h\le N<C$，比较及差值的绝对值不超过 $2C+2$，
而 $2^{W-1}>2C+2$；负一采用同一宽度的二补数，最终carry作为真实门位保留。

在Active上，元数表决定唯一下一动作。
Push先封存Waiting，再以其实际ordinal建孩子，故孩子返回时父存在。
孩子的parent／slot、父的next及child-node全相符才填那一个空字段；
填后恰从Waiting的 $s-1$ 个完整结果变为Active的 $s$ 个。
其他后续域仍空，父的上级parent未变。
完成只在所有 $a$ 个返回齐全时进行，且从保存active-frame取父，
不会误取最近追加的另一F。各Raw阶段晚于完整源扫描，
引理2.3保证不会因helper重用丢失ordinal／slot。

有限E孩子下降严格到更早节点；REF是零孩子查找而非递归展开先前根。
FEND固定Q数，每个Q有有限E树，STORE不新增Q。
故每个Push都有Complete／Return，最终CUR到达固定末端。
Append／Lookup只扫描完整有限前缀，扫描不扩展自己的界限，
元数验证逐位有限，故所有步骤终止。
实际分配给出所有地址，CAP4.3给出每次S的真实 $\phi_K$，
引理2.3及CAP6.1b给出Emit需要的完整字。
PR57.L3于是适用于这里实际构造的forest与程序；
没有把“存在一个编译器”当作所缺生成的前提。$\square$

**定义 6.7（局部错误终点）。** tag／seal／字段、引用、K／f、unary、范围、
结果描述符或父slot检查失败，各有固定Bad(reason)边。
在仍有效的剩余预算内结束／排空本次有界解析，释放可抛工作角色，
构造有限reason字并Raw21封存rb-fault或joint-builder-fault。
其后是FaultHeld：源令牌仍busy，全部十二字仍在 $P$，
没有response-release、计数／行、结算或Entry成功后继。
它不是原执行拒绝；恶构造的源事件不被补写成一次合法拒绝。

## 7. 私有解释、原源写入及真正回应切口

**定义 7.1（保留的解释与释放尾部）。** 在定义6.5实际程序base进入原PR57.D4解释器。
每条记录完整读取四个unary字段，缓存、定位三个操作数，BF(f)，定位目的并WR。
公开定位使用锁存器4；私有操作数0–2与结果3保存至其消费。
所有parser／MUX结果门都在有序STORE之前。
STORE按逻辑 $i=0,\ldots,2N-1$ 通过Resolve写真实源段。
最后一条源WR之后仍执行该记录恢复、terminal-header RD及exit CTL。

再实际准备20上一位response块及真实不可用描述符；
按真实 $\gamma$ 结果引用At16、RD入私有0，用投影BF至3，
At20实际response-base、WR3。这个过程不测试或OUT私有 $\gamma$。
response仍status0时，依原指定区间描述符作完整扫描清理mutable scratch、offset和中间结果，
排除源段、不可变库、保留元数据和response。
然后才执行原response状态／releaseCTL，
其后执行本次唯一CloseFence(response-commit)，保留实际返回的栅栏引用。
保存current-response-ref，恢复恒等角色、Home16，
Tail0／13／15／17／20／21／22／75／76／77，进入ServiceReleased。
此时没有追加 $q,g_c,j,m$ 版本或J／U行，也未归还源令牌。

**引理 7.2（实际原任务语义及raw切口）。** 在两条声明路径上，
上述解释消费的是本次AA库，源回应为原Left的完整一位回应；
源结果是原全候选guard／MUX规则的结果。
每个中间源WR切口均为实际raw源字，不要求它是一棵合法树。

**证明。** 由引理4.5、5.2，每个BANK projection读到
$\langle C,C\rangle$ 补足 $C$ 槽的对应实际位。
SOURCE读到此前真实源 $C$ 的位，经CAP4.3为同一 $\phi_K$ 的实际格。
对实际记录顺序归纳，常量／投影／Boolean表给出(AS.3)及原完整比较的值；
REF的位置先有完整前置计算，所有unused算术臂也执行。
所以(AS.4)是原完整候选的有效性和叶数guard。
这里使用PR57.T1及T2证明中的parser／MUX部分，
不声称其旧内部scatter构造前提在新代码中仍执行。

在STORE前所有旧位及MUX结果已在真实工作格计算完。
执行前 $r$ 个STORE后，恰好源逻辑前 $r$ 位已成为所选结果，
其余位仍为原值；Resolve的单射及新分配不交性给出该不变量。
这就是CAP4.5的逐记录raw论证，不需要中间字可解析。
全 $2N$ 位写完后是完整接受候选或完整旧源。
最后源WR不等于回应释放：其后terminal退出、不可用response写入、清理、
status及release均为实际边。私有投影保存的正是已算 $\gamma$，
故公开完整回应不是Plan的预测位。$\square$

**定义 7.3（ServiceReleased的精确边界）。** 该切口具有：
$P$持全部工作字及busy源令牌；真实response20可用、其引用和两个实际栅栏均保留；
旧／预备计数、原canonical请求、packet／companion、Q／DA／Input22、
$d_P,i_P,I$、代码及两旧端点都有完整记录；
本次 $q,g_c,e,j,m$ 尚未选写，f已包含两个实际栅栏增量。
源是第7节实际最终raw字，目录及 $\xi$ 不变，库仍不可变。
原actor的24–27、种子、旧记录、权限及invocation都保留。
唯一后继是原回应依赖的计数／行延续；不再运行解释、清理、释放或第二栅栏。

**命题 7.4（被替换的精确候选依赖片）。** 选中的C1 Left候选位根
不再依赖PR57.10的slot-zero PAIR、context equality scatter、active-source equality scatter、
OR／PAD fill及只为这些根服务的递归独占前置；其候选值的唯一路径为

$$
F\text{的实际Tag回复}\longrightarrow outbox
\longrightarrow AA\ OUT\longrightarrow Native\ IN/WR\ bank
\longrightarrow BANK\ projection\longrightarrow parser/MUX.
$$

**证明。** 以原选中候选位根为待删集合，递归删除所有活消费者都在待删集合内的前置。
原Left根是slot-zero项、$[s=1+k]$ context项、
$[s=1+M+i]\land A_i\land old_{i,b}$ 源项的OR。
第6节根表用BANK叶逐一替代它们，没有指向这些旧根的REF或固定后备边。
独占的offset、equality、mask、fold、常量因而一并不在选中程序中。
有其他保留消费者的节点不满足删除条件；原context完整检查、
尺寸、全部旧源叶、$A_i,L_i$及sentinel、全parser及carry、所有MUX和Resolve STORE都保留。
Base／Zero的库初始化在实际IN之前，只提供接收区；IN后不重零、
不运行旧构造填值。新pack及元数检查只接触公开元数据，不供应候选payload。
未选中原dispatcher主体仍存在，故此命题只对这一选中依赖片成立。$\square$

## 8. 原行、全部依赖及真正返回状态

**定义 8.1（原计数与行的本次实例）。** ServiceReleased的后继先读取真实已释放 $Y$，
选择预备 $q+1,j+1,m+1$，并仅在 $Y=1$ 时选预备 $g_c+1$，否则选实际旧 $g_c$；
e保持旧值。AppendCounter是唯一新版本写入路径。
最终Left不改 $h,K,r,p,v$；f不恢复，已经包含两个真实栅栏。
按CAP6.2a先写J及index18，再按CAP6.2写U及index19。
J的15个B域严格为：

| 域 | 实际内容 |
| --- | --- |
| 1–4 | SEG-J1；$\xi$；原INITIAL-SOURCE的 $(tag,\xi,H_0,16,b_0,L_0,0)$ 绑定；实际initial $H_0$/prior绑定 |
| 5–8 | $U(j_{old}+1)$；实际旧semantic-predecessor option；原Left event-kind；完整canonical request/material-reference word |
| 9–12 | 完整真实 $Y$；实际六域before/after $q,g_c,e$；本次历史 $U(h)$；完整SEG-SOURCE$(\xi,h,K,v,M_v)$ |
| 13–15 | 实际新 $I$；真实start-fence-ref；真实response-commit-fence-ref |

U的18个B域严格为：

| 域 | 实际内容 |
| --- | --- |
| 1–4 | SEG-U1；$\xi$；实际initial $H_0$/prior引用；$U(m_{old})$ |
| 5–8 | 实际旧unified-predecessor option；原Left kind；完整canonical request-reference word；完整真实 $Y$ |
| 9–12 | before/after $h,K$四元组；before/after layout／policy四元组；before/after $q,g_c,e,j$八元组；before/after committed-directory-count二元组 |
| 13–16 | 完整after-manifest；真实start-fence-ref；真实response-commit-fence-ref；no-publication option0 |
| 17–18 | option1后接真实新J引用；实际新 $I$ |

完整manifest及六域栅栏保持CAP语法；原canonical header／length／payload引用
不被RG packet或AA键替换。拒绝回应不含被拒候选payload。
原行writer使用完整字段、真实Base／长度／sep／status／十域描述符／seal及实际索引写入；
所有会跨helper重用的值先有完整暂存，字段源不会在行目标打开后插入目标块。
semantic索引使用postcommit $j+1$，unified索引使用旧 $m$；
写前分别比较旧索引数与旧 $j,m$，不把新提交计数当作已有索引数。

**定义 8.2（新sidecar与实际依赖复制）。** 只有实际J／U及索引存在后，
P28写NSPROV2的15域：tag；$I$；原A packet-ref；P acquired-call-local-ref；
原A companion-ref；P acquired-companion-local-ref；Q-ref；DA-ref；
canonical request-reference word；$c$；旧CountsEnds7；实际J-ref；实际U-ref；$d_P$；Attempt6。
P-local发生引用在此是provenance key，不自动授予远程读取权限。

原CAP6.3缺失依赖循环完整保留：按原顺序测试并复制缺失boot／initialization／prior，
canonical列出的全部块，再semantic行和unified行。
新读者实际解引用的 $\mathscr D,I,Q,DA$、DA引用的实收元数据、实发ACK、
实收Confirmation及sidecar，也按各自实际描述符在缺失时复制。
复制仍经真实48 mailbox及A28，包含receiver allocation、两阶段拷贝、
状态、seal、copy-completion TOK及每次全池借还；完整origin保留。
guard／proposal／waiting的原保护引用是已取得完整companion载荷内的绑定键，
不是 $P$ 到保护端口的指针。
私有库、候选／parser／结果payload不在此公开依赖集。

行动者逐字完整检查原15／18域、版本、源／boot／prior、全部before／after、
manifest、计数、historical guard、语义mate及两个栅栏，
分别比较旧semantic与旧unified前驱。
再以本地origin解析新sidecar／Q／DA／$I,\mathscr D$，
比较本次原packet／companion／$k,z,c,G_i$／guard／proposal／round／两端点。
全部检查后才安装新joined ends。
所有字回到 $P$ 后，才原whole-row ACK、源令牌TOK回dispatcher、idle CTL，
最后到ComputedReturned。任何copy-completion TOK不替代whole-row ACK。

**引理 8.3（原记录义务与不同前驱）。** 定义8.1–8.2供应本次真实原行及完整依赖，
保留两条前驱链、原拒绝标签和完整返回次序。

**证明。** 引理7.2实际释放Y；因此原phase选择的增量恰对应执行而非预测。
CAP原行合同逐域构造实际manifest及两个已经发生的栅栏，
不会在行内预写自身未来seal或费用。J是本次真实semantic事件，
其前驱是旧semantic端；U是本次真实全事件，其前驱是旧unified端。
U4的Reserve／Raise已经各写维护U，没有J；
它们必须计入m及unified前驱，不能换进semantic前驱。
CAP6.3及CAP引理6.7对各真实封存sender给出完整本地副本及joined checks。
新sidecar只在行后创建，所有指向行的域因此是实际引用；
它不改变原行的字段数或请求／响应。
完整复制／检查、全池归还、原行ACK、source TOK、idle的固定边
实际供应ComputedReturned，不从某个seal推断返回权限。$\square$

**定义 8.4（真正回应状态与唯一新hook）。** ComputedReturned先恢复生产者角色、
Tail13／17，再完整借十二字到 $A$。
重载真实ComputedWait，Close29取得本次 $D_{return}$。
在该完整界内按实际新end及旧m／predecessor选择刚交付U、其真实J，
解析原canonical header／length／完整payload，逐位比较实际waiting的 $k,z$，
并检查sidecar及原call-origin、$c,G_i$、guard／proposal／round绑定。
完整导入真实Y和原行／依赖origins，按RG3.1测量导出并封存新的回应状态25。

仅对这次选中的C1 Left且 $c=$AfterFinal，把其第一条原AfterFinal指令之前
的成功边接入NS_Check。其他返回，包括全部Reserve／Raise，保留原成功边。
NS_Check检查刚封存回应状态与本次sidecar及Plan绑定，
再Close29形成较新的 $D_{catalogue}$，其中已经包含该回应状态及全部交付依赖。
之后才A03保存Wait12，再构造M；原回应状态引用被独立捕获。
未来wait／M／ACK／done的描述符采用真实新ordinal和适当新闭合前缀，
不在较旧 $D_{return}$ 或 $D_{catalogue}$ 内查找它们。

**引理 8.5（结算入口有实际返回数据）。** NS_Check的输入是原真实回应的已封存新状态，
全部十二字在 $A$，源令牌已在dispatcher，原invocation仍持有。
结算等待不使下一Select或下一guard提前运行。

**证明。** 引理8.3先供应原ACK／令牌／idle的完整次序；
RG6.2的真实返回读者后取得新界和新行，
故同值旧行不能以旧origin／旧predecessor替代。
新状态在完整Y及实际origins安装后才seal，$c$测试在其后。
NS_Check在这唯一边运行，全池已经借给 $A$；
保护25／27的token没有转交，后继控制唯一是结算发送／等待。
原下一Entry尚未发生，所以没有未来guard、候选或回复可作为结算输入。$\square$

## 9. 真实返回数据的AA结算及原下一入口

**定义 9.1（实际catalogue和M）。** 在 $D_{catalogue}$ 内使用完整本地引用／origin解析，
按真实base／length／type／flags／status取得各公有载荷。
固定owner-local保护端口读使用ARC保护头导入；
收到的异主引用只通过本地等origin副本解析，不能读异主端口。
建立pending-key及completed-key两个真实列表，初始根为实际J／U／sidecar、
本次原packet／companion、guard／proposal、boot／prior／$\mathscr D,I,Q,DA$。
每次取pending项，全字比较completed；新键才解析、列入catalogue，并加入其固定类型的真依赖。

| 类型 | 递归取得／展开的字段 |
| --- | --- |
| SEG-J1／SEG-U1 | actual prior／initial绑定，两个各自前驱，canonical计数引用表，semantic mate，新代码身份的描述依赖 |
| NSPROV2 | 真实Q／DA／J／U／描述依赖及canonical表；A原packet／companion及已取得完整guard／proposal按本地绑定读取 |
| Q20 | canonical表及 $d_P$；Companion17／Attempt6内的原发生引用保持数据键，其完整载荷已取得 |
| DA6 | Q、六块Response元数据、实际PayloadACK、五块Confirmation元数据 |
| identity | 其两个相同 $d_P$ 作为已有完整描述依赖去重 |
| manifest／fence／计数／完整线元数据／代码描述 | 按其固定完整语法检查；印出的来源／地址／ordinal不是新增能力或任意递归引用 |

依赖和前驱都指向有限既有封存记录；origin-to-local解析键不作为反向边再跟随。
catalogue每项为五个B域：固定role、完整original-origin或local-key、
实际A-local-ref、type、完整已取得payload。相同完整键只列一次。
Count／循环／列表操作采用RCA12.1实际字程序，不用外部字典或随机存取。

M为九B域，随后真实 $U(d)$，随后 $d$ 个五B域项，完整耗尽：

| 固定域 | 内容 |
| --- | --- |
| 1–4 | NSSET2；实际 $I$ 载荷；实际Q原引用键；实际DA原引用键 |
| 5–6 | 完整原canonical request-reference word；原 $c$ |
| 7–8 | 完整旧CountsEnds7；真实检查后新CountsEnds7 |
| 9 | 完整实际释放Y |

M的Q／DA键必须解析为catalogue中的实际载荷项；
它们不是AA能力。catalogue保留即刻所需的真实前驱载荷，
不以不存在的none替代present predecessor。
M无私有源／候选payload镜像。A04完整字库装配、测量导出并封存M，
之后从该真实描述符发送 $U(|M|)$、全部M位、010。

**引理 9.2（catalogue闭合与元数据关联充分性）。** 定义9.1的catalogue有限完成，
供应本次结算读者全部实际解引用的公有载荷。
在引理5.2执行关系下，AA可以不取得Native完整payload镜像而关联原尝试／outbox与本次原返回。

**证明。** $D_{catalogue}$ 是追加前固定的有限记录数，每个记录有有限载荷及有限类型域。
每个新completed键对应这些实际记录之一；重复键全字比较后不再扩展。
前驱虽可递归到更早行，却只在这个有限集合内；
typed字段表不把任意比特子串当作指针，也不沿本地副本origin再回指未取得异主对象。
因此pending的可能新键有限，全部真实取得和列表重建各终止。
每个实际required字段或是完整内嵌字，或由该表加入pending，故全覆盖。

AA已保留Q、封存outbox、所打印Response元数据、实收PayloadACK及生成Confirmation。
其AwaitSettlement／delivered阶段保证这是先前唯一实际已交付尝试。
M内Q／DA及相关元数据全字比对这些真实记录，
由引理5.2而非从DA单字求值，得到同一个不可变Native库。
原任务的Y、J／U及返回不要求被拒候选的完整公开镜像；
它们此时全来自原行及真实状态。
故这一结算读者只需保留关联证明的运行条件和公有元数据，
不需把新权限加给行动者去事后读取16。$\square$

**定义 9.3（AA实际接收、全检查与结算）。** supervisor在实际AwaitSettlement，
逐位backing接收unary长度，真实构造每个1的length mark，
按mark逐位接收M，随后接收并检查全部010，结束前不可解析可用body。
ReadAAFrame先在实际剩余预算内读unary长度并构造marks，
再消耗对应marks复制实际payload；缺位或多位进局部错误。
九次固定ReadFrame后读实际 $U(d)$，对每项五次ReadFrame，最后要求耗尽。
这些是逐bit／next／cursor域读写，不是理想parser原语。

完整比对以下实际资料：NSSET2、同一新 $I$、Q／DA与原尝试及实际transport记录、
原canonical请求、完整Left payload、$c$、两组CountsEnds7、原J15／U18、
不同的两前驱、semantic mate、源／initial／boot／prior／code、
全部before／after计数和目录manifest，以及两个实际六域栅栏及其绑定。
manifest按真实 $U(v)$ 和tag00／01／10的arity6／7／5解析。
引用键只在接收catalogue内全字匹配，返回AA本地backing引用。
栅栏真实性承接本卷Native writer及实际连接的归纳；
AA不由数值相等推断其是meter真读数，也不调用Native meter。

两个原固定驱动器的实际Ready及当前grants都检查后，
分配新binding，逐域写实际前binding-tail、$O,F$实际上下文引用、
原尝试／outbox、实收M／Y／J／U／dependency backing引用及从实收Y读的outcome。
seal最后写。实际outcome1才把current-context槽写为原已拥有的 $F$引用，
outcome0保留／写 $O$引用；再链接完整binding-tail。
根槽、权限及源边不随选择而改写。

**定义 9.4（真正结算ACK及恢复）。** binding seal、实际选择及tail链接后，
AA逐位复制构造并封存

$$
ACK=T_4(\mathtt{NSACK2},I,\text{实际完整实收M},\text{实际outcome}).
\tag{AS.6}
$$

真实干遍历构造长度字，再从封存backing打印 $U(|ACK|)$、全部ACK、010，
通过专用settlementACK连接到 $A$。
行动者A05–A07分别在74接收长度、按真实长度分配body并IN／WR、接收ending。
长度逐位执行IN5、EX74、WR74(5)、RD74(4)、MR74，直到实际0。
body用实际 $U(|ACK|)$ 作计数，逐位执行RD计数、IN5、WR74(5)、MR74、MR计数，
末尾再作一次RD计数的0测试。
ending在新测尾部对三位各执行IN5、EX74、WR74(5)、MR74、ML74、RD74(4)、MR74；
实际RD后继比较对应010位，有限match位保留此前不匹配，三位均接收后才分支。
body在全ending匹配后才精确重载描述符、写status1；坏ending保持body status0。
然后预算ReadFrame恰四次，检查NSACK2、完整 $I$、完整M、恰一位choice及耗尽，
全位比较echo与自己真实M、choice与原真实Y。
重查Wait12及捕获的新回应状态handle／packet／$c$／端点绑定。
通过才A08封存Done8，恢复74头约定，按原RG3.1实际重载捕获的新回应状态，
进入唯一原AfterFinal。

原AfterFinal读这一真实回应，作原参考后继／stage更新，
测量导出并seal原完成轮状态25，十二反向TOK归还 $P$、恒等角色CTL、
Tail13／17及原Entry。其唯一原后继是下一loan／reload／Select，
由真实 $Y$构造Right$(\alpha)$或Rho；尚未取得下一guard。

**引理 9.5（结算、ACK及原消费者串接）。** 第9节把实际新返回状态接到
真实AA结算和ACK，再接到原AfterFinal／Entry／下一回应依赖构造。
成功既不由局部AA ACK代替，也不由外层PayloadACK代替。

**证明。** 第8节已供应真实返回状态及全部原任务记录。
引理9.2给出有限实际公有闭合数据，专用连接的前缀归纳使AA接收body恰等于A发送M。
固定九／计数／五字段解析及完整比较因此全通过，
未改写的原来源、不同前驱和本次实际Q／DA也通过。
两个驱动器在全部内层Return后已经Ready；结算不调用源编辑。
每个binding域来自实际本地引用或实收数据，seal在最后，
故current-context选择指向原已拥有、可调用的固定上下文，不创造引用权限。
ACK只在这些写入后开始构造，其echo是整个实收M。

专用ACK方向、阶段及四域语法不同于内层End／局部ACK、PayloadACK和whole-row ACK。
行动者逐位接收前缀不变量给出同一实际ACK。
Wait和M保存在不同字库域，全位匹配后seal Done，再重载被捕获的新状态，
所以ACK接收辅助工作造成的活跃库重用不会使AfterFinal读取旧状态。
RG6.2的实际完成轮导出、十二TOK及Entry边仍全执行，
下一Select因此在原真实新状态上构造其下一请求。
没有已知future guard用于任一步。$\square$

**命题 9.6（B6star与旧全镜像合同不相同）。** 只施加DA格式及Q／C／L等元数据检查，
而不施加引理5.2的实际运输关系时，这些检查不唯一确定任意 $L$ 位库的内容。
第5、9节不实现要求Native公开完整outbox副本的读者。

**证明。** 固定同样Q、C和L，取两个长度L而某位不同的独立字。
DA只含元数据引用、ACK／Confirmation及flags的格式，
没有该位的payload；脱离忠实连接／实际WR归纳，可以给这两个字配相同元数据。
因此元数据自身不确定payload。
引理5.2额外用实际封存outbox、独占串行连接、逐位backing及不可变性排除这对替换，
结算承接的是这个执行关系。若某旧读者请求被省去的Native公有完整镜像，
其所需取得对象不存在，不能从DA或本卷结算推出。
NSPROV2／NSSET2／NSACK2的版本语法只服务这里明确的新读者。$\square$

## 10. 单一有限接合定理与两条实际分支

**定义 10.1（整段共同配置及交接表）。** 共同配置包括每条真实带／对象的内容与头、
全部锁存器、原生和AA阶段、当前权限、工作字角色、连接满空、
描述符／状态／seal、所有历史、meter、待完成记录及原invocation。
以下21段的配置是顺序执行实际到达的配置，不是分别选择的组件端点。

| 段 | 真实入口至真实出口 |
| --- | --- |
| J00 | 外层有限安装、描述／身份创建及真实复制；两个AA根分配、O七次完整编辑、实收boot-done；原Native准备、种子、mode10 |
| J01 | 原Reserve3、Raise3、Rho、Rho四个完整Lift返回及Entry |
| J02 | 原 $C_0$ Select、实际独立U2、原Plan／Reserve5／Raise5／Rho及全部记录／返回／Entry |
| J03 | 原下一Select构造C1 Left；实际独立U2或U4；U4的原Reserve10、Raise10各完整返回 |
| J04 | 实际最终ComputedWait、A保护头取得、Companion17／74描述符；完整额外49复制／检查／ACK／全池返回 |
| J05 | 原packet49复制／检查／ACK／全池返回，最终十二TOK到P，pair检查及原canonical三块／完整转换 |
| J06 | 原admission唯一源TOK，旧／预备字段、manifest、唯一source-start栅栏、Attempt6／Q |
| J07 | 实际Request打印、AA完整backing／解析检查、实发RequestACK、P完整echo检查 |
| J08 | 实际O Tag检查、Fetch历史／F重放／八编辑／F Tag、封存同Q的outbox、Response打印 |
| J09 | P元数据检查、真实库分配／IN／WR／ending／status、实发PayloadACK／实收Confirmation、DA |
| J10 | 真正Input22／handle，28全解析及嵌套检查、实际后置Base22、BIND |
| J11 | 全forest／FEND、具体E/F验证／Push／Waiting／Return／R、实际Resolve／Copy／Emit、封存完整程序 |
| J12 | 原私有解释、所有parser／旧源／MUX、全部有序源STORE、raw切口、terminal退出 |
| J13 | 不可用response实际私有投影、完整清理、唯一response-release、唯一response-commit栅栏、ServiceReleased |
| J14 | 真实Y选择计数、原J／index18、原U／index19、实际NSPROV2 |
| J15 | 全部原／新缺失公有依赖实际48复制与joined checks、全池归还、whole-row ACK、source TOK、idle |
| J16 | 原ComputedReturned、完整借池、waiting重载、新Close29／全检查、真正回应状态25封存 |
| J17 | 仅选中C1 hook，新的catalogue界、Wait12、真实闭合catalogue／M、逐位发送 |
| J18 | AA真实AwaitSettlement接收／全检查、实际binding各域／seal／choice／tail、真正ACK构造及打印 |
| J19 | A74真实ACK长度／body／ending、完整四域／M／I／Y检查、Done8、头恢复及捕获的新回应状态重载 |
| J20 | 原AfterFinal、原完成轮state25／反向十二TOK／恒等角色／Tail13／17／Entry，下一loan／reload／Select构造原回应依赖请求 |

J09／J10交接时全部字在P，A保护端口／invocation未变，AA在真实AwaitSettlement；
Input22后的新22base是实际测量值。
J13／J14交接时源仍busy，Y已释放，计数尚未追加，两个实际栅栏已存在。
J16／J17交接时字全在A，dispatcher有源token，回应新状态已seal。
J19／J20交接时同一新状态已重载，AA的实际选择已seal并有实收完整ACK。

**定理 10.2（实际原子供应替换及原返回的有限接合）。** 在假设1.2下，
存在定义1–10明确给出的一个有限增广安装 $J$。
对它的实际原beta准备、mode10、$C_0$实际guard $U(2)$，
以及随后C1分别实际供应 $U(2)$ 或 $U(4)$ 的两条路径，
定义10.1给出逐点有限合法完成到原下一回应依赖构造的连通日程，满足：

1. 最终Left的原调用、操作数、守卫、源及AA输入均实际达到；
   O／F有各自真实资源、历史和固定根入口。
2. 选中Left候选依赖片由实际取得的alpha／beta供应值替代，
   这些值真正进入保留的完整原parser／所有MUX／所有源STORE，
   不以fixture库、假定代码或旧构造回退供值。
3. 原真实Y、15／18域行、原依赖／两前驱、whole-row ACK、source-token／idle、
   原返回状态均完整存在；随后AA消费这些真正返回资料并结算，
   实际结算ACK后才原AfterFinal／Entry／下一Select。
4. 对原任务及记录采用各自完整语法和本次实际新引用／代码身份／栅栏／费用的对应，
   不要求旧源身份或完整公开微迹相等；B6star是明确的运行关联，
   不包含旧Native完整公有payload镜像义务。
5. 第11节的费用递推在实际相继配置上有限定义，
   包含新增安装、存储、引用、检查、传输及原全部保留工作。

成功不以未来guard或未来返回值为额外输入。

**证明。** 命题1.5先供应一个真实有限安装及良基身份。
J00中AA当前O内容由真实七次编辑建立；Native随后有自己唯一真实准备。
引理3.2及RG的原完整前缀供应J01–J03：
C0的真正返回先于C1 operand构造，U4维护各自完整返回先于最终Left。
所以此处不是从抽象同名树挑选一个未运行的入口。

引理2.3、2.6和定义3.3供应J04–J06的原所有者、保护头、
packet／companion、全部工作字及旧／预备值。
开始栅栏真实发生后才有Attempt／Q，没有把生成组件的开始栅栏再执行一次。
J07把实际Q送到已有AA驱动器supervisor；
引理4.3、4.5在这些实际输入上构造重放、编辑及outbox。
引理5.2的逐位不变量给出J09真实接收库，
引理2.3和5.5给出真实Input22、解码及BIND。
故J10的每个初始字段都是此前writer的结果，不是组件间假定成功的接缝。

引理6.6供应具体J11程序和真实地址；引理7.2逐记录消费它，
给出原parser和MUX的值、所有raw中间格及真实后继。
J13完整terminal、不可用response、清理、release和commit栅栏供应精确ServiceReleased，
没有把最后源WR当作已经释放的Y。
命题7.4给出实际依赖替换且无选中回退。

引理8.3将真实Y接到完整原行／依赖／检查／ACK／source-token／idle，
引理8.5实际安装新回应状态。
引理9.2的有限公有闭合列表和引理9.5将J17–J20依次接通，
AA的选择来自真正Y，A的AfterFinal也读真正返回状态，
不是读早期Plan位或ACK辅助工作留下的临时库。
所有交接的owner、头、角色、字段、闭合界和固定后继均是定义10.1的同一实际配置。

有限性逐段成立：原前缀有限，AA每个完整调用按AA20.3完成；
有限树遍历及有限历史索引停止；真实线长度和固定ending有有限输入；
所有Raw／解析扫描都以完成字为界；forest由有限 $C,N,W$ 构成，
栈严格下降孩子且Q集冻结；解释器消费完整有限程序；
实际旧栅栏读数不会追赶不断延长的meter尾；
catalogue只在有限闭合界内扩展，最后ACK是已完成有限M的有限echo。
连接日程逐bit使发送接收相邻完成：接收backing才开放下一OUT，
当前方向所需的接收阶段已由上一完整帧建立，没有互等未来尚未生成数据的环。
故假设1.2下每个声称完成的前缀都有限，组合到达实际J20。
这是一安装的两个输入备选，不能把它们拼成同一历史里同时存在的两个结果。$\square$

**推论 10.3（两条真实分支的原消费者）。** 定理10.2的两条路径有下表结果。

| 实际C1输入 | 原维护 | 最终 $h=K$ | $N,M,C,L,W$ | 完整parser的Y | AA实际选择 | 原下一Select |
| --- | --- | --- | --- | --- | --- | --- |
| $U(2)$ | 无 | 5 | 9,9,19,38,54 | 0 | O | Right$(\alpha)$ |
| $U(4)$ | Reserve10、Raise10各完整返回 | 10 | 19,9,29,58,94 | 1 | F | Rho |

**证明。** C1参考原候选是 $\langle D,D\rangle$，有四叶，weight10。
原Plan在guard2时不维护，在guard4时执行严格Reserve10／Raise10。
实际encoded源和context都是 $C$，候选 $\langle C,C\rangle$ 十叶。
前者当前guard5，完整parser因此拒绝；全部十八源位STORE仍执行并选择原位。
后者当前guard10，等号接受；全部三十八源位STORE仍执行，
其中原Reserve真实新增二十源位，旧 $\phi$ 不变。
代入 $N=2h-1,M=9,C=1+M+N,L=2C,W=3N+C+8$ 得表中尺寸。
AA的选择由实际返回Y，原下一构造由原RG8.1同一真实Y决定。
此时下一guard尚未IN，推论不为它赋值。$\square$

**命题 10.4（输入不足及协议失败的范围）。** 若某声明外层输入的后缀没有供应，
本构造不能凭已有元数据越过该IN产生正常完成；
结算或ACK错误也不回滚已经提交的原事件。

**证明。** 库status只在完整payload及ending后置1，
Input22及BANK引用检查需要该真实status；没有旁路旧候选构造。
因此缺payload时实际控制停在相应接收／backing阶段。
AA结算body和A ACK-body分别在完整ending后才可用，
Done还要求完整四域和M／I／Y／Wait匹配；缺失或错误无成功后继。
J13的原源提交早于J17；后段错误只保留故障和已存在的实际行／状态，
没有写回旧source或删除历史的边。$\square$

## 11. 实际相继配置上的完整费用

**定义 11.1（可加工作与存储峰值）。** 对定理10.2的实际联合配置 $z$，
记录Native原语次数（按owner／purpose／opcode）、Native ticks、fees、meter receipts、
构造普通格数、有限控制／代码／类型／token／连接状态位、定位／头移动、
各方向线位、描述符／unary／引用物质，以及AA的分配、
逐域读写、测试、I/O、局部ACK、控制及实际引用表示存储。
这些坐标不以一个Native／AA标量汇率合并。
另以 $S(z)$ 记录当前完整保留存储，用整个实际前缀的最大值作peak，
不能把各组件独立入口测得的peak相加当作共同peak。

展开本卷每条日程及其引用的实际原过程。
在实际return边令可加账 $V=0$；对使 $z$ 到 $z'$ 的实际原语 $e$，

$$
V(G,z,I)=\chi(e,z,z')+V(G',z',I'),
\qquad
P(G,z,I)=\max\{S(z),P(G',z',I')\}.
\tag{AS.7}
$$

IN消费实际供给位；连接IN消费先前绑定OUT的实际位；测试的实际RD／CTL选择后继。
return时 $P=S(z)$。对顺序段

$$
V(A;B,z)=V(A,z)+V(B,\operatorname{exit}(A,z)),
$$

peak取这两个实际连续前缀的最大值。
CTL、失败测试、role置换、status、seal、TOK及每个头移动都计入。
未使能动作无执行费用；未完成输入只有已经执行前缀的账，没有成功return数值。

**定义 11.2（逐族实际展开项）。** 第2节P族的一次 $T_r$ 写入费用为：
各字段真实取得及Raw77快照，New11，各次保存11的Reload及Frame，
Finish11、Copy到1、Raw目标和实际出口定位之和。
Raw包括Base、完整干长度扫描、FieldBody、sep／status0、两个不同输出Add、
全部十域准备、完整旧描述符扫描／ordinal增量／写入、At／WR1／CTL、
真实八域引用构造／复制／置换、Tail目标／17。
原始线字按其实际Frame／FieldBody／字面Append替换对应项。
其payload长度是 $\ell=\sum_s(2|w_s|+1)$，
此外每个字段快照占 $|w_s|+2$ 目标格、完整描述符及其真实引用，
所有工作字／长度字／退役版本也保留计费。

Append22的长度为 $|tag|+1+\sum_s(|field_s|+1)+1$ 个混合符号，
每条支付完整计数、字段预存、各次重载及Tail／WriteField／seal。
额外的E／F／result／parent／slot验证、独立77激活字、Waiting／resumed版本、
TOP／R／CUR、真实dummy三格及描述符全部计费；E仍六域，F仍七域。
AA按每次真实分配与逐域读写支付，bit／next／tail／length-mark、
引用实际编码和内外层backing不能折为一个单位对象。

A族按ARC测量导出及实际字库每次版本重建展开，
另计新Close29、typed闭合列表的全字比较／全扫描／去重／重建、
保护头取得／恢复、Wait／M／ACK／Done及捕获状态实际重载。
没有递归base／length暂存项，也没有免费十三字寄存器。

**定义 11.3（解释、通道、线位与存储式）。** 对实际门 $g$ 的四地址
$v=(a,b,c,d)$，保留TMC PR57.06的实际分组：

$$
I(g)=18+5\sum_{r=1}^4(v_r+1)
       +\sum_{r=1}^4(2h_{g,r}+3v_r+3)+5+P_g.
$$

$h_{g,r}$ 是此前实际步骤达到的头，$P_g$ 全部展开到实际缓存、descriptor-seek、
Home／Last／At及状态／控制操作；At还包括其实际地址字的Last。
末尾terminal RD及exit另计。生成、分配、清理、response、行和返回不在 $I(g)$ 内。

原行长度分别为

$$
\ell_J=\sum_{s=1}^{15}(2|J_s|+1),\qquad
\ell_U=\sum_{s=1}^{18}(2|U_s|+1).
$$

每个实际缺失依赖的原48／49通道除全部setup、Base／Zero、真实描述符、
定位／状态及receiver检查外，支付 $12\ell+6$ 两循环seal／TOK核心，
和四次全池交接的52次原语。whole-row ACK、source TOK及idle另计。
manifest、fence、身份、origin和unary大小均用本次实际字长。

设实际 $q=|Q|$，外层Request、RequestACK、Response、PayloadACK、Confirmation
的线位数依次为 $2q+8,2q+8,2q+C+2L+10,2q+L+9,2q+L+9$，
合为 $10q+C+4L+44$；boot-done四位另计，
两端实际打印／接收／backing／检查与连接控制另计。
完整字段打印／固定接收核心为 $5k+1$，库接收核心为 $5L+1$，不含setup及status。

设M九域为 $f_s$，catalogue条目为 $w_{t,s}$，则

$$
\ell=|M|=\sum_{s=1}^{9}(2|f_s|+1)+(d+1)
             +\sum_{t=1}^{d}\sum_{s=1}^{5}(2|w_{t,s}|+1).
$$

结算线为 $2\ell+4$ 位。Native发送length和ending的每位都是RD、OUT、MR，
body每位是RD计数、RD载荷、OUT、MR载荷、MR计数，末尾再RD计数。
所以length／body／ending核心为 $3(\ell+1)+(5\ell+1)+9=8\ell+13$。
若 $a=|ACK|$，ACK线为 $2a+4$；定义9.4的实际接收给出
length／body／ending核心 $5(a+1)+(5a+1)+21=10a+27$。
全部Last／At／分配／描述符／seal／全解析／全echo比较及AA侧逐域工作另计。
ACK含整个M，不能仅按choice或记录数计费。

Native沿用 $S_N=S_0+b_{control}+8A_N+8n_N$ 的普通格／receipt记账，
其中四个新增边界对为八格，另有四个端口token。
保留源段、scratch、原13块、packet、行／索引／计数、25／27及退役版本，
再计描述／身份两端及通道副本、companion三份载荷、75／76／77全部backing、
不可变库 $L+2$ 格及引用／描述符、Input22、28域及嵌套暂存、DA／sidecar、
全部forest／字段预存／stack版本、字面15程序、dummy及每个结果三格／十域描述符。
清理写0不返还已构造格。
AA保留两套真实源／header／路由带、初始化及重放请求／回复、链接、
八编辑记录、Tag／路径／栈／outbox、Q／transport／AwaitSettlement、
完整M／catalogue／length-marks／binding／全M echo的ACK及所有实际引用表示。

**命题 11.4（整段完整递推及有限值）。** 定理10.2两条实际路径的完整账
是(AS.7)在J00–J20真实相继配置上的求值，逐段包含：

$$
\begin{aligned}
&V(\text{字面安装、描述／身份及复制、AA初始化与boot-done})\\
&+V(\text{原Native准备、种子、Lift、C0及U4实际维护的全部原返回})\\
&+V(\text{companion保护头／导出／额外通道、原packet通道、最终借池})\\
&+V(\text{原canonical／转换、旧／预备值、manifest、唯一开始栅栏、Q})\\
&+V(\text{真实AA查询／重放／编辑／Tag、全部外层线与库／DA})\\
&+V(\text{Input22、28全重解析／嵌套检查／暂存、BIND})\\
&+V(\text{全forest／向量／计数／预存／扫描、E/F验证、真实栈／结果／Emit})\\
&+V(\text{原解释及全部源STORE、response私有投影、清理、释放、唯一提交栅栏})\\
&+V(\text{计数选择、原J/U及索引、sidecar、全部缺失依赖／检查／原ACK／token／idle})\\
&+V(\text{原返回读者／新状态、新闭合界／Wait／catalogue／M、AA结算／ACK})\\
&+V(\text{A真实ACK接收／全检查／Done／头恢复／新状态重载})\\
&+V(\text{原AfterFinal／新完成状态／反向借池／Entry／下一Select}).
\end{aligned}
$$

每一加项的入口取前项实际出口；所有可加坐标及实际存储peak有限。

**证明。** 第2–9节每个新块都有实际字长、base、ordinal及明确writer，
所有循环／测试／CTL／I/O都在(AS.7)中有原语或逐域转移。
旧过程以定义1.1给定的实际展开参与，而非赋一个服务常数。
定理10.2的有限完成使递推有有限项数。
每项只分配有限格／对象及有限表示字，所以存储前缀的最大值有限。
Native每个实际原语一receipt、一tick、两fee，故其分量为 $n_N,n_N,2n_N$。
加入较早暂存／验证改变后续头、unary地址、描述符及栅栏数值；
因此必须在新出口重新求后项，不能在旧总量上加一个修正常数。
没有重复的开始／释放／提交尾部，也没有省去新增引用和扫描的计费。$\square$

## 12. 精确对应与仍然不同的研究问题

**定义 12.1（本定理的对应范围）。** 定理10.2对应的是新安装 $J$ 内
原调用合同的真实请求、原完整回应、真实源／目录转移、
原行语法／两前驱／全部实际新引用及原返回消费者。
每个真实联合后继仍是定义10.1的全部配置，
不被已复制到行动者的公有投影代替。
AA事件是其各自根的真实新事件；Native事件是其唯一实际准备谱系的事件。
旧RG、$G_H,G_V,G_C,G_O$ 的启动身份、完整微迹、地址、时钟和收费
不因合同复用而变成 $J$ 的身份或数值。

本卷承重内容是具体来源上的供应值到原候选消费者、实际行返回及结算的有价接合。
AA的历史重建、原请求／字段／解析、有限门生成及兼容递推方法
分别沿用定义1.1的准确数学引文；本卷不把这些一般方法另作新基础。

**定义 12.2（未由此有限接合给出的目标域）。** 下列量词及对象
不在定理10.2的结论域内：整个供应器族的替换；任意Busy／内部／all-cut当前取得；
四个可独立使用表达及其原消费者；原original-Q的新行、cross-entry和全终止核；
更广alpha／beta实际操作桥；后继guard以及另一轮所需的真实新speculative源；
实际物理载体；全资源比较及全局／Pareto最小性。
两条路径结束于原下一构造，未代替原Stop／INITIAL终止任务，
也未把两个已经使用的AA根当作任意重复的新资源。
第11节给出逐点完整递推，不赋予任何数字整段运行总量、优势或统一无界重复的有限资源上界。

## 追加锚（本行以下为增补区）

## 13. 两阶段原子供应的对象、量词与完成前提

**定义 13.1（单元及对应范围）。** 本节至第25节构造一个新的原始启动安装
$J^*=\mathtt{JCOMP2\text{-}OI\text{-}F7C1}$。其原消费者仍是 RG8.1 的
mode10 消费者，最终任务仍是 RG1.2 的同一次初始准备上的 INITIAL-$q_1(\beta)$。
两个原子供应位置恰为它实际到达的最终 C1 Left，以及由该 C1 真正回应选择的
最终 C2 Right 或 Rho。原 Lift、C0、所有维护、所有原返回和原终止路线继续执行。
这里的“执行”是下述顺序源模型中的构造日程；正文给出普通数学证明，
不声称存在已运行的装置、已执行的 resident 表或 Lean 核验。

沿用定义1.1的 $D=\langle\beta,\alpha\rangle$、$B=\langle D,\beta\rangle$、
$C=\langle B,D\rangle$、$E(t)=\rho^2(t)$。
以下把候选容量记为 $c_{\rm cap}$，不与树 $C$ 混用。
$U(n)=1^n0$，$B(x)=U(|x|)x$，$T_r$ 为恰 $r$ 个 $B$ 域的串接；
树名 $B$ 与帧构造 $B(x)$ 依参数区分。
Native 令牌仍为 PAIR11、alpha01、beta10、PAD00。
AA 的 Tag 回复编码仍是定义4.1的另一种编码，须逐次转换。
物质 unary 标记不是逻辑叶，也不是待编辑的逻辑地址。

完整输入域为：本安装自己的 beta 准备、种子及 mode10；C0 实际输入 $U(2)$；
C1 实际输入 $U(2)$ 或 $U(4)$；在该次 C1 完整返回、结算、ACK、捕获状态重载、
原 AfterFinal、Entry 和下一 Select 之后，才独立输入 C2 的完整 $U(g)$。
前一种 C1 要求任意有限整数 $g\ge2$，后一种要求任意有限整数 $g\ge4$。
这是同一安装的两类备选运行，未把两个 C1 结果放在同一历史内，
也未将未来守卫写在启动数据中。$g$ 是参考守卫，$h,K$ 是当时实际 encoded 状态；
$g_c$ 表示接受修改计数，避免与守卫 $g$ 混淆。

**假设 13.2（逐点材料、权限与真实输入）。** 保留假设1.2、AA20.1、
CAP 的原语／寻址／描述符／栅栏／通道及 ARC、RCA、RG 的字库、准备、调用和返回合同。
每个宣称完成的运行还满足：

1. 所需源、记录、端口及连接权限当前独占且有效；固定连接忠实；没有并发写者、撤权、崩溃或中断。
2. 本次运行所需的有限新材料和工作存储实际供应，包括第三驱动器、所有控制行、类型、
   holder、marker、任意长的实际引用、各退役版本和终止副本。并不假定跨运行统一的有限容量。
3. beta、模式、每个声明守卫及每个规定确认均在其使能输入处完整供应；每个 $g$ 有限。
   原先验与控制器在实际到达的计算处终止。未完成输入只有已到达的前缀。
4. 第14节的根槽、驱动器、grants、连接及有限辅助寄存器都在这一次原始启动实际安装并计费。
   分配或一个编码引用本身不供应调用边、端口令牌或权限。

这些前提不包含 Input22、bank、生成代码、真实回应、结算或 Handback 已经完成。
所需入口由以下构造供应。源模型内的逐点有限完成不推出物理实现或统一时间界。

**定义 13.3（三种角色）。** 在最终 C1 等待点，committed Native 源为 $C$，
AA 的 $O$ 也为 $C$；原 Left 的实际 encoded context 另为 $C$。
C1 的新候选源为 $F=\langle C,C\rangle$。
C1 真实释放 $Y_1$ 后，封存 binding 选择 $O$（$Y_1=0$）或 $F$（$Y_1=1$）。
随后维护只改变原布局／guard，不编辑这一已选 AA 源。
C2 原请求分别为 Right$(\alpha)$（encoded context 为 $D$）或无 context 的 Rho；
其新候选由第三根 $N^*$ 产生，分别为 $\langle C,D\rangle$ 或
$\rho(\langle C,C\rangle)$。旧源、请求 context、新候选、Native 准备发生 $\xi$、
Native bank 引用及 AA 事件来源均是不同对象。

## 14. 一个原始启动中的有限安装与真正 C1

**定义 14.1（载体、固定入口与保留资料）。** 保持 RG0–73 的全部原所有者，
采用定义1.3的 A74 和 P75、76、77，不增加第十三工作字。
P16 保留私有源／工作 arena，P17 保留描述符，P21 保留完整暂存块，
P22 先写 Input22 再写另测起点的 forest；A29、A64–68 保留原语法及所有者。
A25／27、源16／17的令牌不进入十二字借用。每次借用完成十二个 TOK 与阶段 CTL 后才运行 helper。

实际安装三个互异、源无关的 AA20.2 驱动器 $D_O,D_F,D_N$ 和一个有限 supervisor。
三个根槽各只初始化一次，只写各自分配器返回的真实根引用。
固定 CallO、CallF、CallN 三个分支各有自己的当前源／记录 grants、scratch、
请求／回复、End、局部 ACK 及同根 Return 连接。
保留定义1.3的五条外层有向连接，第二条按互斥阶段传 boot-done、RequestACK、
Response、Confirmation；另完整构造并计费 $D_N$ 的内层连接束。
每个方向的端点、满／空、锁存、backing 和阶段状态均实际存在。
invocation、源服务令牌及十二工作令牌始终分开。

supervisor 另有真实字段：stage、initial/current selection、previous sealed binding、
当前 attempt、三个固定驱动器 handle、重放游标／链、旧叶 frontier 链、源全字检查缓存、
两次 M／ACK 及部分接收字段。它们是分配的记录；长度、索引、路径和栈可以是任意大的有限数据，
不成为运行时扩张的有限控制标签。原始 previous-binding 为 null，initial-context 槽为 $O$；
初始选择标签只指定已装 $O$，不授予新权限。

**定义 14.2（类型、行表及身份的良基顺序）。** 所有旧类型字原样保留。
先把原 RG／CAP／本卷过程与本增补的 stage 分支作 hygienic 有限联合：
两种字库奇偶、三个固定驱动器调用、三个 return case、全部 writer／reader／fault 分支均在表内。
各静态 helper 调用点内联并有字面返回边；运行时引用与地址只存在于有 backing 的字或字段。
按定义1.4的文字序展开 Native／AA 行，有限新类型包含两 stage 的 Q24、Companion20、
source-witness、selected-receipt、receipt-carrier、binding、prepared-e-plus、sidecar、
结算 Wait／M／Done、ACK 及各 pack-field／frame 快照；原有同类算法及端口不变。

在这些有限新类型之后，按下表的严格顺序续编 F7C1 的21种类型；表中 $s=1,2$ 分别代入 N1、N2：

| 先后 | 新类型 |
| --- | --- |
| 1 | `N2-RHO-NO-CONTEXT-F7C1` |
| 随后 $s=1$ | `N1-INPUT22-F7C1`，`N1-F7-HANDLE-F7C1`，`N1-F7-REF-COMPONENT-1` 至 `N1-F7-REF-COMPONENT-8` |
| 随后 $s=2$ | `N2-INPUT22-F7C1`，`N2-F7-HANDLE-F7C1`，`N2-F7-REF-COMPONENT-1` 至 `N2-F7-REF-COMPONENT-8` |

仍用原旧表最大长度 $m_0$ 和全表依次下一个 $i$，编码为 $1^{m_0+1}0U(i)$。
不重置 $i$，故 marker、T、holder、字段快照及两个新 Input22 类型彼此不同且不碰旧类型。
Input22 第1域使用相应 `N1-INPUT22-F7C1` 或 `N2-INPUT22-F7C1` 名称的固定 ASCII 比特编码，
其描述符使用相应新类型字。这个原子入口只接受上述新版本；旧 Input22 标签不作 Rho 的另一入口。

先形成全部有限 $R_N^*,R_A^*,\mathcal R^*$，再由表外的实际安装边逐位写入行表及

$$
\mathscr D^*=T_4(\mathtt{JCOMP2\text{-}OI\text{-}F7C1},
 \operatorname{enc}(R_N^*),\operatorname{enc}(R_A^*),\mathcal R^*).
$$

在 P21／17 完成其载荷、十域描述符及 status 后取得实际 $d_P^*$；随后写

$$
I^*=T_4(\mathtt{RBG1},d_P^*,d_P^*,\mathtt{1100100000010}),
$$

取得实际 $i_P^*$。两块完全复制到 A，A-local 引用各异，origin 分别为 $d_P^*,i_P^*$。
新21类型及所有新增有限行都属于此描述。resident 表不含自身描述或未来描述符数值，
表外安装边也不被其自身所安装的表循环描述。此后每个身份、地址、ordinal 与 fence 均取本运行新值。

**定义 14.3（原始启动与前缀）。** 实际分配 $O,F,N^*$ 为三个 alpha 根，
初始化其 parent／left／right／header 域，并绑定各自驱动器。
在 $O$ 完整执行 (AS.1) 的七项
$P_\varepsilon,S_\varepsilon,S_L,P_R,S_{LL},P_{LR},S_R$；
每项都消费 Growth、End、局部 ACK、同根 Return，完成全部祖先 Maintain。
$F,N^*$ 保持 alpha／Ready。其后才发送并 backing／检查 boot-done0010。

再执行本安装自己的 CAP／RG 单次 beta 私有 ingress／验证、源初始化、计数器／目录、
boot／prior、stationary seed 取得和完整种子返回。
按 RG2.2 保存真实原 Stop 表24、原配置25、空 waiting27、头距离及初始化绑定，
在第一次 RG append 前将其完整字存入互异持久字段；mode10 与转入 RG 槽的 invocation TOK 均真实发生。
不借用旧 $J$ 的 seed、$\xi$、行、引用或已到达对象。

原 Lift 的 Reserve3、Raise3、Rho、Rho 各走完整调用与返回；
C0 原 Select 构造 Rho，独立接收 $U(2)$，完整返回 Reserve5、Raise5、最终 Rho。
其原 Entry／loan／reload／Select 才构造 C1 Left$(D)$ 的参考提案和其 encoded operand。
C1 真正输入 $U(2)$ 时不维护；输入 $U(4)$ 时原 Reserve10、Raise10 各完整返回，
随后到最终 C1 ComputedWait。全部维护保留原 canonical 主体、依赖、ACK、token、idle 及状态安装。

**引理 14.4（新安装自身的共同内容边界）。** 在假设13.2下，定义14.1–14.3
给出有限原始安装，并在两种 C1 输入的最终等待点真实达到：Native 源为 $C$，
原 encoded Left context 为 $C$，$O=C$/Ready，$F=N^*=\alpha$/Ready。

证明。有限类型、端口、字段号和调用点组成有限表；所有变量循环使用实际有限字或链。
定义1.4–1.5的先行表、后描述、后引用、后身份顺序适用于新表，并排除未来描述符依赖。
AA17.2、20.3 与引理3.2的七项逐步源计算在三个独立根中的 $O$ 上适用；
第三根没有被该过程编辑。Native 的真实 beta 种子、原四次 Lift 与 C0 完整返回
分别给出 $E(\beta)=B$、C0 参考后继 $D$ 和 Native 后继 $E(D)=C$。
原下一 Select 从该真正状态复制 $D$，原两次替换／前序转换产生 context $C$。
Reserve10／Raise10 只扩展实际 $\phi_K$／guard，保持旧源、原地址及 waiting。
所以两种路径均有上述边界。早期 AA 与 Native boot 源不相等；所需内容不变量从此边界开始。
所有根和 $\xi$ 的身份仍彼此不同。$\square$

## 15. 实际等待、来源见证、选择回执与 Q24

**定义 15.1（由真实状态构造的旧源见证）。** 每次指定最终调用发送前，A 完整重载
该次封存 ComputedWait，构造并在74测量导出／封存

$$
S_w=T_4(\text{wait-origin},\text{完整wait载荷},t,\operatorname{tok}(E(t))).
$$

$t$ 是由实际 seed 及已安装真正返回所得到的 reference tree 字。
两次替换和前序展开以有限栈／字运算实际执行：叶追加其替换字，branch 保留次序，
压右后压左；每个栈项、位和计数都写入。该见证不读取 Native 私有源。
P 取得全字，检查 waiting、$\xi$、stage、round、origin，并从完整 $t$ 重算 $E(t)$。
supervisor 通过已选固定驱动器的逐次 Tag 遍历得到实际旧源全字，
与 $S_w$ 的末域比较全部位及结束。这个检查不再把旧源等同于 Q 的请求 context。
wait 中的 Native 发生引用是数据键；只有已声明、已取得本地块的 typed reader 才解引用。

**定义 15.2（上一结算的真实回执）。** C1 的 selected-receipt 是只能选已装 $O$ 的
初始 tagged case。C1 真正结算 ACK 完整收到、检查并封存 Done 后，A 在74另写不可变
stage1 receipt-carrier，保留完整实际 $M_1,ACK_1$ 的已完成引用、各 A-local 引用及 Done origin。
C2 构造 companion 前重新 Close29，按该特定 carrier 的引用／类型／status 取得完整载荷，
导入完整 $M_1,ACK_1$ 和发生绑定；不用一枚会被状态重载覆盖的 scratch 位。

AA 自身保留封存 $B_1$、实收 $M_1$、实发 $ACK_1$、已 delivered attempt。
C2 比较回执的完整 M／ACK、$I^*,Y_1,Q_1$、J／U origins 和 Done 谱系与这些真实记录。
因此 stage2 只能由 $B_1$ 选择固定 $O$ 或 $F$；外来引用不决定未安装入口。
旧源 Tag 检查还须通过本次新 $S_w$。carrier、见证和选择 binding 各有自己的对象与作用。

**定义 15.3（Companion20 与原请求）。** Companion20 保留定义3.3的17域，追加3域：

| 域 | 完整载荷 |
| --- | --- |
| 1–5 | 本 stage 的 Companion20 版本；实际 packet27-ref；完整 packet；实际 waiting25-ref；完整 waiting |
| 6–10 | 完整 $G_i$；实际 guard-ref；完整参考守卫字；实际 proposal-origin；完整 proposal |
| 11–14 | $\xi$；实际轮 $U(i)$；previous-semantic-end；previous-unified-end |
| 15–17 | 原 $k,z,c$ |
| 18–20 | 当前已装 consumer stage；完整 $S_w$；定义15.2的 selected-receipt option |

先实际 route49 复制 companion，检查、ACK、全池返回 A；再 route49 复制原
$T_4(\mathtt{RG\text{-}CALL2},k,z,c)$ packet，完成同样全路线；最后才十二 TOK 到 P。
原 canonical header／length／payload 三块在13／17按 CAP4.6实际构造，引用表计数仍为3。
Left011、Right100 的 $z$ 通过完整原 prefix parser／converter；Rho001 的 $z$ 是真正空字，
长度块表示0，payload 块仍实际有零长度载荷、sep、status 和描述符。
$S_w$、receipt 和 companion 不是加到原 canonical 引用表的 context 块。

**定义 15.4（Q24 的完整字段及唯一 admission）。** P 在原 admission 只取得一次源服务令牌。
完整取得实际旧 $h,K,r,p,v,q,g_c,e,j,m$ 与两端点。
按第17节先完成本次 F7Stage／F7Handle；旧值与五个互异预备加一字
$q^+,g_c^+,e^+,j^+,m^+$ 也在角色重用前分别完成。
完成 before-manifest 后仅执行一次 source-start CloseFence，保留真实载荷／引用。
随后构造 Attempt6 和下列 Q24；所有子字／独立 Raw77 字段快照都先于父前缀：

| 域 | 完整载荷 |
| --- | --- |
| 1–4 | 当前 Q24 版本；完整 Attempt6；companion-origin；完整 Companion20 |
| 5–7 | 原 call-origin；完整 canonical 三引用字；原实际 $z$ |
| 8 | ContextOption：graft 为 $1\Vert T$；Rho 恰一位0 |
| 9–10 | graft 为 $1\Vert U(d),1\Vert U(M)$；Rho 各恰一位0 |
| 11–15 | 实际旧 $U(h),U(K),U(r),U(p),U(v)$ |
| 16–18 | $U(N),U(c_{\rm cap}),U(L)$ |
| 19–20 | 本次已发生 start-fence 的完整六域载荷；实际 $d_P^*$ |
| 21–24 | 实际原 operation tag；当前 stage；完整 $S_w$；selected-receipt option |

Attempt6 仍恰为 call-origin、companion-origin、round、guard-ref、$c$、start-fence-ref 六域。
各 option 在自己的 $B$ 域内独立解析并耗尽；Rho 的 $B(0)=100$ 不是 reference。
graft 要求 $d\ge1,M=2d-1$。每处尺寸检查实际重算

$$
N=2h-1,\quad
c_{\rm cap}=\begin{cases}1+N+M,&\text{Left／Right},\\3N,&\text{Rho},\end{cases}
\qquad L=2c_{\rm cap},\qquad W=3N+c_{\rm cap}+8.
$$

Rho 没有 $d,M,T$ 值，不采用 $M=0$。C1 的 $d=5,M=9$，C2 Right 的 $d=2,M=3$。
这些数来自实际转换。h 取维护后的原状态，不以 $g$ 替代。
old CountsEnds7 和真正维护后的 unified end 保留于旧状态／companion，
与 $G_i$ 的 preceding selected-final origin 分别检查。

P 与 AA 都全字比较 call／companion／wait／guard／proposal／source／receipt／stage／round／origin。
operation 必须同时符合 canonical header、Q24.21、stage 和已装返回 case：
`RBC1LEFT`、`RBC2RIGHT` 或 `RBC2RHO`，各与真正 caller-kind、
$c=$AfterFinal、ComputedReturned、ServiceReleased 对应。
AA 只在 stage1 真实结算及完整 ACK 打印后接收 stage2；RequestACK 回显实际收到的完整 Q24。
从 admission 到首个源 STORE，全部新增工作保持源、目录和旧计数；f 只随实际 fence 前进，不恢复旧 f。

## 16. 三个固定根上的真实历史与两类 C2 候选

**定义 16.1（C1 供应及内层完成纪律）。** 每次 CallO／CallF／CallN 从对应驱动器的
实际 Ready 开始，完整写出定义4.1的三位请求及地址／索引字，逐位发送；
收到完整 tagged reply 和 End 后先封存 backing，才局部 ACK。
等实际同根 Return、scratch cleanup 和 Ready 后才运行保存的后继。
Navigate／Guard 每次重新检查实际路径、逻辑 arity、目标类型和当前权限；
Maintain 沿每一个实际祖先维护真实 tape。无引用值被转作调用目标。

C1 先 Tag 遍历 $O$，压右后压左，比较完整结果与 $S_w$ 的 $C$，
另比较真实 graft context 的转换字。随后从实际 $U(1)$ 开始 FetchGrowth，
每个 Recall 都保留 kind／完整路径，以该 acquired kind／path 在原 fresh $F$ 重放，
封存索引、旧 Recall 和新 Growth 的重放链接。只有真实 OutOfRange 才结束；七不是循环输入。
再完整执行 (AS.2) 的八项

$$
S_{LLL},P_{LLR},S_{LR},S_{RL},P_{RR},S_{RLL},P_{RLR},S_{RR}.
$$

由引理4.3–4.5和 AA17.2、19.2、20.3，$F$ 在自己的根／历史上变为
$\langle C,C\rangle$，共有15个成功增长事件；没有把 $O$ 的源边、parent、header 或 tape 搬到 $F$。
新 stage／见证检查只增加辅助工作；本次所有引用与地址照实际重新构造。

**定义 16.2（C2 Right 的实际构造）。** 真正 $Y_1=0$、$B_1$ 选择 $O$ 后，
原 Select 才构造 Right$(\alpha)$；其实际 encoded operand 是 $D$，旧源是 $C$。
$N^*$ 仍是本安装从未编辑的 alpha／Ready。经实际 $B_1$／receipt／$S_w$ 检查后：

1. 在 $D_N$ 完整执行 $P_\varepsilon,S_\varepsilon$。
2. 在 $D_O$ 实际 FetchGrowth$(1)$，要求完整 Recall 为根处 $P_\varepsilon$，保留它并只跳过此出生提升。
3. 从索引2继续实际 FetchGrowth 到 OutOfRange；每个 Recall 的路径前缀加 L，
   在 $D_N$ 执行其真实 kind，并完整消费 Growth／Maintain／End／ACK／Return，封存重放链接。
4. 在 $D_N$ 完整执行 $P_R,S_R$。$O,F$ 无编辑。

**引理 16.3（Right 的出生类型及源顺序）。** 定义16.2在假设13.2下合法有限完成，
得到自己的 $N^*=\langle C,D\rangle$；成功增长为4次 P、6次 S，根路由带为 $L^6R^2$。

证明。$O$ 的实际 alpha 出生历史是 $P_\varepsilon;H^-$。
新根 P／S 后，左孩子出生 beta，右孩子出生 alpha。
已取得并跳过的恰是旧 alpha 根变 beta 的第一项；$H^-$ 是从 beta 出生根构造 $C$ 的合法后缀。
AA17.2 对该后缀每一实际前缀适用；加 L 后各路径由 $D_N$ 的真实 Navigate 到达，
在更深祖先处的 Maintain 也实际增加对应 L。
六项后左子树为 $C$；最后 P_R／S_R 把右 alpha 变为 $D$。
故树的括号、次序和标签均为原 Right 的整体候选，而非只有叶数相同。
原历史有限，OutOfRange、逐次完整内层返回与两项尾部给出有限性。
若不跳过第一次根提升，则会在新 beta 左孩子调用 P；该非法前缀不能用历史重放名义略过。
根的两个自身事件不记在其路由带，其余六左、两右事件给出所列 tape。$\square$

**定义 16.4（C2 Rho 的实际构造）。** 真正 $Y_1=1$、$B_1$ 选择 $F$ 后，
原 Select 构造无 payload 的 Rho。检查当前 $F=\langle C,C\rangle$ 的全 Tag 字与新 $S_w$；
在 still-fresh $D_N$ 上从索引1到实际 OutOfRange，逐个重放 $F$ 的真实 FetchGrowth Recall，
每项完整返回并写自己的重放链接。十五是所得事件数，不是预置停止条件。

此时先让 $D_N$ 源静止，Tag 栈遍历并封存恰好其逻辑叶的地址／已取得 alpha、beta 标签链。
branch 继续压右、压左，物质 unary marker 不入链；整链完成后才允许下一源编辑。
按该旧链顺序：旧 alpha 地址调用 P，旧 beta 地址调用 S，每项全回复及 Return 后才前进。
新生逻辑叶不追加到旧链。这里调用的是已装 $D_N$ 的三位接口，
不调用未装 LAB 宏控制器，也不要求 Tag 返回其语法中没有的对象引用。
目标引用的持久性是证明不变量；真正引用由驱动器内部 Navigate／Guard 在每次调用重新到达和检查，
不由 supervisor 传入绕过权限的引用操作数。

**引理 16.5（旧 frontier 的完整 Rho）。** 定义16.4合法有限完成，
保持旧 $F$ 不变，得到 $N^*=\rho(\langle C,C\rangle)$，
其 alpha／beta 叶数为 $(6,10)$，有16叶、31个活跃令牌。
$D_N$ 共执行10次 P、15次 S。

证明。AA19.2的真实 Fetch 和 AA17.2 的逐前缀合法性先给出本根上
$\langle C,C\rangle$ 的十五次完整重放，含6次 P、9次 S。
其旧叶为4个 alpha、6个 beta，且源是 AA 的非 alpha 可达成员。
不同旧叶路径两两前缀不可比；在某项编辑不会移动另一项的实际根引用，
也不改其源子树。因而下一旧项的已取得标签仍当前有效，实际 Guard 通过。
逐项原操作把旧 alpha 变 beta、旧 beta 变 $\langle\beta,\alpha\rangle$，
原 branch 和左右次序保持。LAB9.3–9.4 的旧 frontier 结构归纳因此在此真实历史上适用，
得到整棵 $\rho$，不是对新生叶再替换一次。这里只复用其结构论证；
实际接口、寻址与权限仍是上述 $D_N$。
新增4次 P、6次 S，故总数及叶对如陈述。
有限树／旧叶链和 AA20.3 的完整内层返回给出终止。$\square$

**定义 16.6（候选 outbox）。** C1 在 $F$、C2 在 $N^*$ 完成编辑后，
再作完整 left-first Tag 遍历，将每个真正回复转为两位 Native token 并逐位追加。
实际计数活跃令牌，消耗收到的完整 $c_{\rm cap}$ 字，补 PAD 到恰好该容量；溢出为局部 fault。
全部位、长度和本 Q 关联写完才封存 outbox，才允许 Response 打印。
候选值只来自这个实际 Tag 字。状态计算的 $S_w$ 只检查旧源一致性，不供应候选位。
$N^*$ 在 C2 使用后保持 spent／Ready，不重置为 alpha、不重新绑定、不供第三原子轮。

## 17. 强制第7域的真实块、holder 与完整 Input22

**定义 17.1（操作索引的第7域）。** 本安装每个 Input22.7 都是强制的完整 CAP6.1
八域 reference，而非 option reference。令本次 writer 真实返回

$$
r_7=T_8\bigl(\operatorname{ownerWord}(P),\operatorname{portWord}(17),U(c_7),
 \operatorname{portWord}(21),U(b_7),U(\ell_7),\tau_7,U(b_7+\ell_7+1)\bigr).
$$

owner／port 使用 CAP 不变的 $U$ 编码；$c_7,b_7,\ell_7$ 均从实际完成描述符取得。
第7域对父字的贡献是 $B(r_7)$。

| 实际操作 | P21 中的真实 payload | 长度 $\ell_7$ | 描述符类型 $\tau_7$ | 与 Q24 的关系 |
| --- | --- | --- | --- | --- |
| C1 Left | 实际原 $z$ 转换后的完整 $T=\operatorname{tok}(C)$ | $2M=18$ | N1-T | Q24.8 恰为 $1\Vert T$ |
| C2 Right | 实际原 $z$ 转换后的完整 $T=\operatorname{tok}(D)$ | $2M=6$ | N2-T | Q24.8 恰为 $1\Vert T$ |
| C2 Rho | 本次新构造的一位字0 | 1 | N2-RHO-NO-CONTEXT-F7C1 | Q24.8 恰为0，与取得 payload 全字相等 |

两个实际转换的后果分别为 `111111100110111001` 与 `111001`；
这些显示字不是替代 parser／converter 的启动常量。
Rho marker 是 source-free 的 absence witness；它不是 T、两位 token、空树、
source／AA 根引用、$M=0$ 或供 context parser 消费的字。
Rho 的实际 $z$ 另由 Raw21 写成长度0块；其 sep／status／描述符真实存在，
与这个长度1 marker 完全不同。

**定义 17.2（F7Stage 与真正 holder）。** F7Select 先取得并验证原 packet、
Companion20、stage、canonical 三块及 $z$。
graft 运行完整原 prefix parser／converter，实际得到 $d,M,T$；
Rho 检查 tag001、零 payload 长度、空 $z$ 和全部 absent options。
不在失败分支构造替代字段。

P 持完整十二字及原 admitted 源服务阶段，先将无关活值暂存，再只执行一次本 stage 的 F7Stage：
graft 用静态 N[s]-T 类型 Raw21 写真实转换字；Rho 用 New／Append0／Finish
构造一位0，并用其独立 marker 类型 Raw21 写入。
Raw 严格采用定义2.1：Base21；完整干长度扫描；FieldBody；sep／status0；
不同输出 Add 构造状态地址；在十个角色准备全部域、实际完整旧 P17 计数及 creation 加一；
Tail17、描述符 tag00、十个 WriteField 和 seal；实际 At／WR1／CTL；
再构造八域引用、Copy 到 role1、恢复角色、Tail21／17。
其真实十域描述符为

$$
(P,21,b_7,\ell_7,c_7,\tau_7,1,0,b_7+\ell_7+1,\varepsilon).
$$

这里 P／端口／数值按各自原编码写入，origin 为空；mutable0 表示可用后不可改写。
目标尚开时没有嵌套 Raw 或快照调用，也不在77保存目标自身活跃 base／length。

F7Stage 返回且目标完全关闭后，把**返回的整个 $r_7$ 作为 payload**，
Raw77 写入该 stage 唯一的 `N[s]-F7-HANDLE-F7C1` 块。
这个 Raw77 返回的是 holder 自己的 reference $r_H$，不是 $r_7$。
后来须以 $r_H$ 或此串行 stage 的实际有界 type／ordinal 扫描取得 holder 载荷，
才能重新得到真正 $r_7$。不得把 $r_H$ 填入 Input22.7。
holder 自己也有实测 length、sep、status、描述符和空 origin；本 stage 消费前没有同类型覆盖边。
同值旧 T、旧 marker 或别的零块均不能代替本次已存 $r_7$。

F7Stage／F7Handle 完成后，才完成原旧态／五预备增量、manifest、唯一 source-start 及 Q24 父装配。
Q24.8 从已完成 option 字装配并与第7域 payload 对应；Q 不含未来 Input22 或 holder 引用。
marker 和 holder 不在任何活跃 Q／P27 前缀内分配。
该辅助工作不写源、不新增 admission、response、NativeLocal 行或源事件 fence。

**定义 17.3（新版 Input22 的完整28域）。** 完整 RequestACK、Response、私有 bank、
PayloadACK、Confirmation、DA 已按第19节取得后，才逐字段准备下表。
每个子元组和每个字段都有独立 Raw77 pack 快照；尤其第7域先读 holder 的整个 payload $r_7$，
再保存 P27-field7 快照。28个字段依次为：

| 域 | 完整内容 |
| --- | --- |
| 1 | 当前 stage 的 `N[s]-INPUT22-F7C1` ASCII-bit tag |
| 2 | 实际可用 bank 完整引用 $r_B$ |
| 3 | 实收原 call 的实际 P-local-ref |
| 4 | 实收 Companion20 的实际 P-local-ref |
| 5 | 原 canonical request-reference word，实际 count3 和三个完整引用 |
| 6 | 实际原 $z$ 的 staging-reference，Rho 亦有真实零长度块 |
| 7 | 定义17.1–17.2本次实际 $r_7$ |
| 8 | $T_6(dOption,MOption,U(N),U(c_{\rm cap}),U(L),U(W))$ |
| 9 | 实际旧 $h,K,r,p,v$ staging-reference 五元组 |
| 10 | $T_2$（旧 $q,g_c,e,j,m$ 引用五元组，互异预备 $q^+,g_c^+,e^+,j^+,m^+$ 引用五元组） |
| 11 | $T_2$（旧 semantic-end option，旧 unified-end option） |
| 12 | 实际取得的完整 $G_i$ 的本地 staging-reference |
| 13 | $T_2$（原 guard-ref，实际完整 acquired-copy ref） |
| 14 | $T_2$（原 proposal-ref，实际完整 acquired-copy ref） |
| 15 | $T_2$（原 waiting-ref，实际完整 acquired-copy ref） |
| 16 | 完整实际 Attempt6 |
| 17 | 实际 Q24-ref |
| 18 | 实收完整 RequestACK-ref |
| 19 | $T_2$（完整实收 Response 元数据 reference-table，实际 DA-ref） |
| 20 | 实发 PayloadACK-ref |
| 21 | 实收完整 Confirmation-ref |
| 22 | 本次真实 start-fence-ref |
| 23 | 实际 before-manifest-ref |
| 24 | $T_4(\xi,boot,prior,seed)$ 原绑定完整字 |
| 25 | $T_2(d_P^*,i_P^*)$ |
| 26 | $T_5$（原 caller-kind，实际 $c=$AfterFinal，ComputedReturned，已查 RBC1LEFT／RBC2RIGHT／RBC2RHO，ServiceReleased） |
| 27 | 恰九位 `111110000` |
| 28 | $T_5$（实际 call-origin，guard-origin，proposal-origin，round，previous-selected-final-origin） |

第8域前两项与 Q24.9／10 是同一完整 option 字；其余为实际 unary。
第27域前五位记录 bank-ready、echo-checked、response-complete、payloadACK-sent、
confirmation-checked；后四位 settlement、source-write、candidate-read、candidate-parser-read 为0。
它们不代替独立验证。

全部快照完成才 New11，依次 preserving-Reload／Frame28次，Finish11、Copy 到1，
Raw22 写新版 Input22；其真实 P17 描述符和 status1 完成后才提供 handle。
活跃11前缀内只运行定义2.2允许的 Reload／Frame／FieldBody／字面操作，
不打开 P21／22／77 的另一个目标，不用父自己的 base／length 作 backing。
Raw 的十域加两个临时角色、Reload 的1–10及保护11／12仍遵守引理2.3，始终只有十二字。

## 18. 全字段、全嵌套读取及实际后置 BIND

**定义 18.1（外层和操作先行的完整读取）。** ReceivedBankEntry 的 handle 本身不授 token；
此时 P 已实际持全部工作字和所需端口／源服务阶段。
先 Raw21 归档该真实 handle，再解析其八个 B 域引用和实际十域描述符，
检查 P／17／22、ordinal／base／length／新 stage type、initialized1、mutable0、空 origin、
seal、status 地址等式、实际 At／RD status1 和 P22 范围。

对 $j=1,\ldots,28$ 是28个固定分支。每一遍从实际 Input22 base 重启全长预算，
完整执行28个 ReadFrame，检查预算耗尽及物理 sep，仅在11保留第 $j$ 域；
**整遍结束后**才 Copy／Raw21 写 stage-qualified field-j 快照。
包括 Rho 在内，第7域在每一遍都作为完整 $B(r_7)$ 被消费。
不因 none 而跳过、不把该域解作0，也不在提前识别 Rho 后截断扫描。

在解释第7域 referent 前，先完整解码取得的 call、Companion20、Q24、其实际 typed dependencies，
以及第26域恰五个 return 字段。
从真实 canonical $k,z$、Q24.21／22、waiting／stage／round／receipt 和 RBC case 的共同检查
确定 Left／Right／Rho。描述符类型不能自己决定 operation，也不能决定已装根。

**定义 18.2（八域引用、holder 与真实描述符）。** 重载完整 field7 快照，
以其实际全长预算解析恰八个 B 域、耗尽并检查 staging sep。
用八个静态完整 reparse 分支，每遍只保留一个组件，遍末才写入第14节的对应新组件类型。
完整检查 owner／port／ordinal／base／length／type／status 的 canonical 编码。
在已完成的 P17 前缀内实际有限扫描本 stage 唯一 holder，检查其十域、seal、status，
取得其整个 payload，逐位及两端比较为同一个 $r_7$；不以 Raw77 的返回 handle 代替此 payload。

在 nested descriptor 扫描／输出快照前冻结完整 P17 计数 $D_7$。
$c_7$ 必须选中该界内的完整记录；ordinal 是扫描键而非头位置。
每个组件检查都作从起点的完整 tag／字段／seal 扫描，一次保留一域，扫描后才保存。
十个 descriptor 域全部与
$(P,21,b_7,\ell_7,c_7,\text{expectedType},1,0,b_7+\ell_7+1,\varepsilon)$ 比较，
其中 expectedType 来自定义18.1已定操作。
状态地址以真实 unary Add、不同输出及比较构造；实际 At／RD 要求 status1，并检查 P21 arena／range。
后续快照有自己的新 handle 及包含它们的新适当闭合界，不拿 $D_7$ 查未来快照。
不接受 unavailable descriptor、同类型 LatestType 的别块、异主地址或只有数值 origin 的载荷。
writer／holder／Input22 的串行先后和 immutable 保存共同证明该引用来自本次早先 F7Stage。

**定义 18.3（两个 payload 分支及 option 的精确接合）。** graft 在实际 $b_7$ 按预算复制
恰 $\ell_7$ 位到完整字，消费并检查物理 sep 和当前 status。
原 $z$ prefix parser／converter 和完整 token-tree 检查全部保留：
要求 $d\ge1,M=2d-1,\ell_7=2M$，取得 payload 与真实转换结果全等、两端耗尽。
Q24.8 必须是初位1后恰该完整字；Q24.9／10及 Input22.8 前两项
必须逐项恰为 $1\Vert U(d),1\Vert U(M)$。none、余位和 marker 类型均失败。

Rho 在 marker 实际 base 按长度1预算读恰一位并要求0；然后预算0、物理 sep、status1。
要求独立 marker 类型、空本地 origin、$\ell_7=1$ 及本次 holder 全 $r_7$ 相等。
Q24.8／9／10各恰单比特0，第8域前两项也各恰0；
原 canonical tag001、空 payload／$z$、stage2 和 RBC2RHO 必须一致。
这只产生内部有限控制 case `NoContext-validated`；不产生 T、d、M、context vector、空树解析或新 context 引用。
因此 inline Q24.8 的0与实际 marker 的0是需检验的字相等关系，前者不是后者的 reference。

**定义 18.4（其余嵌套 reader 的完整义务）。** 嵌套元组也只在全预算解析并检查结束后保存选择域。
ReadUnary／ReadFrame 逐 bit 消耗已完成预算，空域仍返回空字；缺终止、越预算或余位均失败。
所有 reference 都按 CAP6.1 的八域／十域／seal／实际 status 路径读取。
本地字段读自身端口；外来来源只解析到已有 equal-origin 的可用本地副本。
完整检查表如下；没有“已解析”一位取代这些 reader。

| 真实对象 | 全部语法及交叉检查 |
| --- | --- |
| 原 request-reference word | 读实际 unary count3，再恰3个完整 reference frame，耗尽；取得 header3位、完整 unary length 和相符全 payload，各自 sep／status／origin；与 call 的 $k,z$ 全比对 |
| Companion20、Q24 | 分别20、24次 ReadFrame 并耗尽；原17域与实际完整 packet／waiting／guard／proposal／两端点相符；新 stage／source-witness／receipt 逐项全解析；Q 的三个 option 按定义18.3 |
| $S_w$ | 恰4域、耗尽；完整 wait 按 RG3.1状态语法解码，逐项检查保存源／boot／prior／seed／stage／round／计数／两端点／真正回应谱系，重算 $E(t)$ 全字；内含发生键不自动当指针 |
| selected-receipt | 初始 tag 只在 C1 选择 O；present case 完整取得并解析实际 $M_1,ACK_1$、A-local refs／Done／carrier 绑定，按第21节的九域／计数／五域及四域语法耗尽；AA 与自身 retained $B_1$／attempt 比较 |
| 旧态与预备增量 | 第9域恰5引用；第10域恰2组、各5引用，读取 $h,K,r,p,v,q,g_c,e,j,m$；重新 Add1 比较五个互异预备字；与实际 ReadState／counter／Q 的旧值相等 |
| 两端点、$G_i$、guard／proposal／waiting | 第11域两 option；第12域完整 RG.4 的版本、$\xi,i,s_-$、preceding-final、guard-ref、proposal-origin、完整守卫；第13–15域各完整原／副本绑定，逐项全比对本次 occurrence、单调守卫、原 proposal／ComputedWait、两种前驱而不混同 |
| Attempt6、fence、manifest | 恰6域 Attempt；start-ref 解析真实六域 fence，kind／$f$／tick／fee／$\xi$／事件目录绑定与 Q24.19相符；manifest 按实际 $v$ 和 tag00／01／10 的6／7／5元数全读、耗尽，与 before-state 相符 |
| transport、DA | RequestACK 的完整头、echo-length、Q 全 echo及ending；Confirmation另查完整 $U(L)$；Response 六块引用；DA6 的 Q、六块 Response、实发 ACK、五块 Confirmation及flags；全部取得载荷、origin 和本次唯一 attempt 相符 |
| 安装及返回 | 第24域恰4原绑定；第25域恰2实际引用，取得 $I^*$ 恰4域并要求两个描述引用均为 $d_P^*$；第26域恰5字段及固定返回映射；第27域恰9位；第28域恰5发生绑定 |
| 尺寸和 bank | 第8域恰6字段，按实际 operation／h 重算全部 $N,c_{\rm cap},L,W$；$r_B$ 的实际描述符为 $(P,16,b,L,c_R,T_{bank},1,0,b+L+1,\varepsilon)$，全引用／seal／status1／arena／非别名检查；不读取 candidate bit |

完整 guard 字是实际 acquired $U(g)$，原 $G_i$ previous-final 与维护后 waiting 的 unified-end
各按自身来源验证，不能只因轮号相同便认同。
任何 foreign key 只有在其类型声明确实解引用且本地 payload 已取得时才跟随；其余作为完整数据比较。

**引理 18.5（真实后置入口）。** 在假设13.2及前述实际 writers、transport 完成的共同配置上，
定义18.1–18.4全部通过后，恢复规定角色／头，才测量此时实际 Base22，保存 rb22-start，
按定义6.1追加／封存三域 BIND$(r_B,\text{actual-call-local-ref},\text{actual-Input22-ref})$，进入 BuildForest。
所有 Input22／sep／status、解码快照及其 appended 材料严格位于该起点之前。

证明。引理2.3给出实际 Raw21 referent、真正 $r_7$、独立 holder 与父28域。
逐字段全 reparse 归纳给出其确切快照；八次引用和十域扫描将其接回同一个已完成 writer，
而不只得到一个语法上可能的 numeral。
graft 的完整转换及三 option 比较，或 Rho 的 typed 一位 payload／空原调用／全部 absent 检查，
穷尽所装三个 stage-operation case。其余完整 reader 将每个读取接到实际早先块。
全部有界扫描在保存输出前关闭，工作字不超过定义2.2的角色数。
最后 Base22 在所有这些步骤之后，BIND 保持原 arity3且引用本次实际新版 Input22。
所以引理5.5的 forest 入口在 graft 上有真实 T，在 Rho 上有真实 NoContext 分支和全部尺寸，
没有尚待构造的强制字段。$\square$

**命题 18.6（fault 与执行拒绝的区别）。** 第7域缺失、literal0／空域／optional-reference、
旧 T／旧 marker／同值别块、错误 stage／type／length／origin／status、Rho 假树／$M=0$、
graft none 或任何尾随位均不能进入上述 BIND。
失败按定义6.7在有效剩余预算内排空、写固定 reason、进入 FaultHeld；
没有本次 release、计数／行、结算、成功 Entry 或伪造 $Y=0$。
缺输入只保留真实前缀／status。已经发生的较早真实提交不回滚。
相反，合法完整候选在真实 guard 不够时仍进入第19节完整程序并释放真正拒绝回应。

证明。前三种 field7 表示不是八 frame reference；其他情形分别被完整身份、descriptor、payload、
option 或操作联合检查排除。坏检查的固定后继不通到 BIND。
原执行拒绝则在所有这些检查通过后由私有 parser／guard 计算，走完整 STORE 和返回路线，
两者的控制路径与记录义务不同。$\square$

## 19. 忠实取得的 bank 与完整原程序

**定义 19.1（五帧运输及逐位不变量）。** 采用定义5.1的实际连接日程，将 Q 换为本次 Q24，
容量／长度换为本次 operation 的 $c_{\rm cap},L$，完整线字仍为

$$
\begin{aligned}
\mathrm{Request}&=0001\,B(Q)\,010,\\
\mathrm{RequestACK}&=1001\,B(Q)\,010,\\
\mathrm{Response}&=1100\,B(Q)\,U(c_{\rm cap})U(L)\,\mathrm{outbox}[L]\,010,\\
\mathrm{PayloadACK}&=1010\,B(Q)\,U(L)\,010,\\
\mathrm{Confirmation}&=1011\,B(Q)\,U(L)\,010.
\end{aligned}
$$

P 在76逐位 backing 所有实收元数据和全 echo；unary 以 IN／EX／WR／RD-test／MR
读到真实0，定长部分用完整计数字逐位 IN／WR后再推进两头。
每个 latch 在其 WR 前不覆写。AA 的 RequestACK、Response、Confirmation也先有完整封存 backing。

Response 元数据检查后，Base16 测新 $b$，Zero 保留 L位和 sep，追加 status0，
写实际不可用十域 bank 描述符。每个实际 AA OUT 位经 IN 后直接 WR 此 bank，
完成 backing 才开放下一 OUT。第 $t\le L$ 位后，双方实际游标、已消费计数和 bank 前 $t$ 位
均与此 attempt 的封存 outbox 前 $t$ 位一致，status 仍为0。
完整 payload 和 ending010检查后，精确重载 descriptor／status，才 At／WR1／CTL 可用。
实际 $r_B,c_R$ 从此描述符取得。P 完整发送 PayloadACK；AA 全字接收检查后才标 delivered，
从该实收 ACK 构造 Confirmation；P 完整取得并检查，才写 DA6及第17节的 Input22。

引理5.2的逐位归纳遂证明这个不可变 bank 恰为本次 outbox。
这是真实独占 writer／忠实连接／IN-WR 的 B6star 运行关系，
不是仅从 Q、DA、长度、flags 或全 echo 推出 payload 的证书。
未建立该运行关系时，等长异字仍可配同一元数据，命题9.6的界限继续适用。

**定义 19.2（forest 的完整保留面）。** 从引理18.5实际 BIND 开始，
原定义6.1–6.5的原生记录语法和完整 machine 原样展开：
E6、Q3、F7、R2、TOP1、CUR1、BIND3、FEND2、VBIT3、VEND2、BUILD6。
每条有真实 tag、全部 sep 域和 seal；Append22先完整计数／逐域预存，后打开目标；
Lookup 一次只选一域，完整越过各记录及 seal，多个域重复全扫描。
K／f 的固定元数和真值表严格采用定义6.3，不放宽错误 K、错误8位表、
非正／不更早孩子、缺省孩子非 U0、REF 非较早 EXPR 根等条件。

具体生成顺序为：

1. 对全部 $s<c_{\rm cap}$ 和 $b\in\{0,1\}$ 写 BANK E／EXPR Q，
   value 是本次实际 $T_3(U(c_R),U(s),b)$，两个 bit 根都有 VBIT backing。
2. 写全部 $2N$ 个 SOURCE 叶，保留原 $A_s=[X_s\ne PAD]$、
   $L_s=A_s\land\neg A_{s+1}$ 和 $A_N=0$，以及所有原来保留的旧源／mask 消费者。
3. 写完整 $W$ 位 parser、全部运算臂及最终 guard，随后全部 $2N$ 个
   $\operatorname{MUX}(\gamma,candidate_i,old_i)$ EXPR 根。
4. 仅在这些结果根齐全后，按 $i=0,\ldots,2N-1$ 追加全部有序 STORE Q。
   所有向量有完整 VEND，BUILD 保存逐槽旧标量／向量；全部完成后 FEND 才冻结实际 Q数和 forest记录数。

graft 入口仍有完整实际 T 和原转换检查；Rho 入口只有通过检查的 NoContext、
完整 $N,c_{\rm cap},L,W$、bank／call／新版 Input22 BIND 及旧态，
没有 context vector，不运行 graft-only routine，也没有 field7 expression leaf。

**定义 19.3（完整 parser 与全部算术臂）。** 使用私有标量 need $n$、closed $z_c$、
leaves $\ell$、valid $v_c$，初值为 $(1,0,0,1)$。每个候选槽完整计算

$$
\begin{aligned}
P&=[token=PAIR],&A&=[token=alpha],&B_\beta&=[token=beta],\\
\Lambda&=A\lor B_\beta,&T_c&=P\lor\Lambda,\\
I_{bad}&=([token=PAD]\land\neg z_c)\lor(T_c\land z_c),\\
n_*&=n+[P]-[\Lambda],&
n'&=\operatorname{MUX}(T_c\land\neg z_c,n_*,n),\\
\ell'&=\ell+[\Lambda\land\neg z_c],&
z_c'&=z_c\lor[n'=0],&v_c'&=v_c\land\neg I_{bad}.
\end{aligned}
$$

扫描恰 $c_{\rm cap}$ 槽后才计算

$$
\gamma=v_c\land z_c\land[n=0]\land[1\le\ell]\land[\ell\le h].
$$

PAD 在 closure 前、非 PAD 在 closure 后均破坏 validity；没有私有提前结束。
所有加法按 PR57.07 的每位五门
$t=x\oplus y,s=t\oplus c,u=x\land y,v=c\land t,c'=u\lor v$，包括最终 carry；
减法逐位 NOT 第二操作数，以 carry1 进入同一加法。
equality逐位 NOT-XOR 后 AND；比较按 PR57.08完整七门递推，signed 比较先翻转符号位。
所有初始常量／复制、MUX 的三个孩子、选不到的 need-minus-one 等臂也真实生成和执行。
公有整数位以真实 unary 倍增、Compare／Sub 和 VBIT 方向重排取得，不预置 h 的向量。
宽度 $W=3N+c_{\rm cap}+8$ 与引理6.6的范围估计适用：
未选 $n_*$ 在 $[-1,c_{\rm cap}+1]$，叶数至多 $c_{\rm cap}$，
$2^{W-1}>2c_{\rm cap}+2$；因此未选臂及最终 carry 也有规定意义。

**定义 19.4（生成、地址与私有解释）。** 每个 EXPR 使用定义6.4的真实
Active／Waiting／Push／ChildReturn／RootReturn machine：先封存 Waiting 再建孩子，
孩子的 parent／slot／node、父 next 及空 slot 全相符才追加新父版本；
返回结果是先实际分配的一位 mutable／available W引用，所有跨 helper 活值均有77快照。
REF 只查较早根的真实 R，不递归复制旧证明或跳过尚未生成的结果。
Q 只枚举 FEND 的固定集合，后来 F／R append 不扩展它。

真实分配不可变一位0 dummy 及其 descriptor／reference。
每个 BANK Emit 重载 $c_R,s,b$，比较 BIND.bank 全引用、实际 descriptor／status，
实际计算 $2s+b<L$ 和 $b_B+2s+b$；不 RD candidate bit。
每个 S 操作数和 S目的都调用当前 Resolve，所有 W地址来自实际分配及 unary Add／Copy。
按定义6.5完整写出每条
$1f_0\cdots f_7U(d)U(a)U(b)U(c)$，常量／一元门的三个 unused address 也存在并指真实 dummy。
代码 Base15 在本次实际生成前测，terminal0后测长度、写 sep／status0、真实 descriptor／status1，
At 该实际 base 才进入不变的 PR57.D4私有解释器。

该解释器逐条读完四地址，执行全部缓存、seek、BF、目的 WR 和恢复。
所有 parser／MUX 结果先于每一个源 STORE。
完成前 $r$ 个 STORE 后，逻辑源前 $r$ 位恰为所选结果，后缀仍是旧位；
由 CAP4.3–4.5的单射稳定 $\phi_K$ 与非别名归纳成立，途中 raw 字不必是合法树。
全 $2N$ STORE 完成后仍有最后记录恢复、terminal-header RD、exit CTL。
随后实际分配不可用 response20，把真实私有 $\gamma$ 经投影 BF 写入，
完整扫描清理规定 mutable scratch／offset／结果，排除源段、immutable bank、T／marker／holder及保留元数据。
最后才执行原 response status／release，再唯一 response-commit CloseFence。
保存 current-response-ref、恢复全部规定角色和头，达到 ServiceReleased；源 token 仍 busy。

**命题 19.5（原语义、真实拒绝和替换边界）。** 在上述共同配置及假设13.2下，
C1 Left、C2 Right、C2 Rho 的原 guard 回应分别由完整10叶、7叶、16叶候选实际计算。
接受时写完整候选，拒绝时全部 $2N$ 个 MUX／STORE 仍执行并保留旧位；
高于当前 h 的 reserved 源位、原 $\xi$ 和稳定旧地址遵守 CAP 合同。

证明。引理16.3、16.5及引理4.5给出实际候选整树；定义19.1前缀归纳把其全字接到实际 bank。
第17–18节供应每一 mandatory 字段及本次 BIND。
引理6.6的 forest／frame 归纳与 PR57.L3适用于这些正的有限 $N,c_{\rm cap},W$；
PR57.T1与 T2 的完整 parser／MUX 部分给出上述 guard 及完整选择，
不借用其已被替换的内部 candidate scatter 执行前提。
逐 STORE 和 release 尾部归纳给出真实原事件及真正 Y，Plan 位不供应回应。

准确删除范围是选中操作的 candidate-bit 根及其全部活消费者都在该删除片中的前置：
Left 的 slot-zero／context／source equality scatter，Right 的 last-active／equality scatter，
Rho 的 chunk／offset scatter 不再作为候选后备。
有其他活消费者的旧源、activity／last-active／sentinel、graft完整检查、全 parser、carry、MUX、
有序 STORE 均保留；未选 resident 主体、旧 archive、旧程序、bank 和 STORE 效果不删除。
因此候选值路径只有实际 Tag、outbox、OUT、IN／WR bank、BANK projection、parser／MUX。
Rho marker 不在此值路径上。$\square$

## 20. 真正回应后的原计数、双链记录与 typed 依赖

**定义 20.1（释放之后才选版本）。** ServiceReleased 后先读完整已释放 $Y$，
用实际旧字和五个互异预备增量，经原 AppendCounter 唯一路径选择

$$
q'=q+1,\quad g_c'=g_c+Y,\quad
 e'=e+Y[\mathrm{operation}=\mathrm{Rho}],\quad j'=j+1,\quad m'=m+1.
$$

Left／Right 保留旧 e；接受 Rho 用本次 $e^+$，拒绝 Rho 保留旧 e。
三个最终操作都保持 $h,K,r,p,v$；f 包含实际两个 fence 增量，不用旧 f 覆盖。
维护已分别贡献真实 $m$、布局／guard／unified行，不贡献 semantic 行。

原 J15/index18先写，原 U18/index19后写，各域全部实际构造：

| 原行 | 按原次序保留的完整字段 |
| --- | --- |
| J 1–4 | SEG-J1；$\xi$；INITIAL-SOURCE 的 $(tag,\xi,H_0,16,b_0,L_0,0)$ 绑定；实际 initial $H_0$/prior 绑定 |
| J 5–8 | postcommit $U(j+1)$；旧 semantic-predecessor option；真实 Left／Right／Rho kind；完整 canonical request/material-reference word |
| J 9–12 | 完整真实 Y；before／after $q,g_c,e$ 六元组；本次历史 $U(h)$；完整 SEG-SOURCE$(\xi,h,K,v,M_v)$ |
| J 13–15 | 实际 $I^*$；真实 start-fence-ref；真实 response-commit-fence-ref |
| U 1–4 | SEG-U1；$\xi$；实际 initial $H_0$/prior 引用；旧 $U(m)$ |
| U 5–8 | 旧 unified-predecessor option；同一真实 operation kind；完整 canonical reference word；完整 Y |
| U 9–12 | before／after $h,K$ 四元组；before／after layout／policy 四元组；before／after $q,g_c,e,j$ 八元组；before／after committed-directory-count 二元组 |
| U 13–16 | 完整 after-manifest；真实 start-ref；真实 commit-ref；no-publication option0 |
| U 17–18 | option1 加本次真实 J引用；实际 $I^*$ |

写前完整扫描 index18／19，分别与 staged old j／m 比较已有 count。
J 用 postcommit j+1，不把它当已有索引数；U 用 old m。
semantic 前驱是旧 J端，unified 前驱是旧 U端，维护只在后者链上。
manifest 按真实目录全写，两个六域 fence 是本次已发生读数，不在行内预写自身 seal／费用。
原引用表仍指实际三块 canonical header／length／payload；被拒候选 payload 不进入原拒绝回应。

**定义 20.2（sidecar、复制与真正返回）。** 行及索引存在后才写 stage-qualified NSPROV2，
15个语义字段仍为：tag、$I^*$、A原packet-ref、P acquired-call-local-ref、A原companion-ref、
P acquired-companion-local-ref、Q24-ref、DA-ref、canonical reference word、c、old CountsEnds7、
实际 J-ref、实际 U-ref、$d_P^*$、Attempt6。
每个字段先完成再打开父目标；没有 Input22 或 marker 作为新增 sidecar 字段。

保留 CAP6.3原缺失依赖次序：boot／initialization／prior，原 typed request 枚举的所有块，
semantic 行，unified 行；新读者实际解引用的 $\mathscr D^*,I^*,Q24,DA$、
实收元数据／实发 ACK／Confirmation、sidecar，以及 Companion20 中实际需要的公有见证／回执资料，
也必须先实际取得／复制。每个48复制都实际 receiver allocation、mailbox、两阶段全拷贝、
status／seal、copy-completion TOK、全池借还。foreign reference 只通过本地 equal-origin 副本解析。

A 完整检查15／18域、版本／$\xi$/boot／prior、全部 before／after、operation／e、
历史 h、manifest、semantic mate、两个各自前驱、identity／fence／canonical 全字及 sidecar／Q绑定，
才安装 joined ends。全池回 P 后才 whole-row ACK、源 TOK 回 dispatcher、idle CTL。
这些边完成才有 ComputedReturned；copy TOK 或最后 source WR 均不代替它。

ComputedReturned 先规范 P角色／Tail13、17，再完整借池给 A，重载特定 ComputedWait，
Close29取得新的 $D_{return}$，按真实新端、old count／predecessor／origin选刚交付 U及J。
完整取得 canonical 原 $k,z$ 和新 Y／依赖，复核 waiting／sidecar／Q，
测量导出并封存真正新回应状态25；不能以旧 LatestType 行、Plan 或旧回应状态代替。
恰两类 hook 位于这个 seal 之后、第一条原 AfterFinal 指令之前：C1 Left，C2 Right或Rho。
所有维护等其他返回保留原成功边。

**定义 20.3（局部与公有 typed closure）。** 依赖边由实际 typed consumer 的解引用决定；
比特形状像引用不产生一条边。下面给出本安装所有受第7域影响的消费边界。

| 对象／reader | 实际取得和依赖边 |
| --- | --- |
| 新版 Input22／P完整 decoder | P17闭合界内解析全部本地字段；第7域指真实 P21 T或marker。它是 P-local acquisition，不走48／49 |
| F7 holder／P身份 reader | P77 完整 payload 是 $r_7$，由实际有界 type／ordinal／descriptor／status读出；holder-reference 与 payload-reference 分开 |
| T／P graft reader | reference-free token 字，完整原 conversion／tree grammar；token 不当 descriptor |
| Rho marker／P absence reader | 终端语法恰0；无 source origin、tree child、嵌套引用或 AA context；不成为公有 catalogue 项 |
| BIND／FEND／E／Q／F／R／TOP／CUR／BUILD／生成代码 | P-local forest／解释 reader；BIND保留真实 Input22 handle；BANK只跟 BIND.bank 及实际 bank descriptor，不用第7域供候选；任何 Input22重载均用新版 decoder |
| 公有 Q24 | AA请求、A返回／结算、AA结算 reader；跟原 canonical 表及 $d_P^*$，全解析 inline三 option；Q无 $r_7$、holder 或 Input22引用 |
| Companion20／$S_w$／receipt／carrier | 完整内嵌语法；实际已取得的 $M_1,ACK_1,Done$/carrier谱系由其声明 reader取得；完整 wait／state内其他 Native／异主发生引用仍只是数据键 |
| NSPROV2／DA／$I^*,\mathscr D^*$／J／U／canonical／M | 跟原公有 roots、两前驱、semantic mate、实际 Q／元数据／描述及实际 acquired本地副本；无反向origin解引用，无 Input22／$r_7$／holder／marker新增根 |
| 原 terminal snapshot／verifier／receipt consumer | 只读原 canonical count3、真实 J／U、原初始化／prior／control／output依赖；marker不加到请求、原行、snapshot请求材料或 target |

原 P-local T／marker／holder 的 origin 为空；公有复制保持各自 origin-to-local 规则。
没有公有 reader 解引用 Input22或第7域；AA检查的是 Q 的真实 absent option 和原 Rho 空 payload，
不假称从不存在的导出 Input22读取了 P 的 marker。
局部正确性由 exclusive writer／完整 decoder 归纳承担，正如 B6star 不能被元数据证书替代。

**引理 20.4（closure 与双链的接合）。** 上述公有依赖取得及局部读取供应每个实际 reader 所需载荷；
不需要发布 marker、holder、Input22或私有候选镜像，也不省略真正被解引用的公有对象。

证明。局部第7域边止于早先已完成的有限 reference-free T／marker，不含未来或循环依赖。
holder的唯一串行 writer及完整 payload 比较固定本次身份。
公有 closure 仅在实际已完成的 A29封存前缀上，按声明边加入 pending、按完整键去重；
两条前驱向既有行递归，local副本 origin 不反向跟到异主。
每个所需对象或为完整内嵌字，或为有本地取得块的明列依赖。
CAP6.2a–6.3的原完整检查遂适用于本次真实 operation及双链；
新增 source-free字不计原事件，真实原回应／记录／ACK／token／idle路线没有缺边。$\square$

## 21. 两次完整结算、真实 ACK 与原下一入口

**定义 21.1（闭合 catalogue、Wait 与 M）。** 真正回应状态已seal、全部交付依赖已取得后，
A重新 Close29冻结 $D_{catalogue}$，独立捕获该特定回应状态 handle。
依定义9.1用真实 pending／completed 列表，在此有限界内全键扫描／比较／去重。
初始根是实际 J／U／sidecar、原 packet／Companion20、guard／proposal、boot／prior、
$\mathscr D^*,I^*,Q24,DA$；stage2还保留其真实 prior $M_1,ACK_1,Done$/carrier读者所需谱系。
每个新键按定义20.3 typed 边完整读取，在本地 reference／origin下取得实际 base／length／type／flags／seal／status。
没有 arbitrary-payload pointer search，也不把缺失 predecessor 改为 none。

每个 catalogue 项仍恰5个 B域：role、完整 original-origin或local-key、实际 A-local-ref、
type、完整已取得 payload。递归 J／U、canonical、DA、identity按定义9.1处理，
Companion20、$S_w$、receipt按定义18.4处理；闭合界外未来 Wait／M／ACK／Done
使用各自后来适当的新界，不在旧 $D_{catalogue}$ 查未来记录。

先在互异持久字段保存 Wait12：stage版本、捕获的新回应状态-ref、原 waiting-packet-ref、
实收 sidecar-local-ref、c、旧 CountsEnds7、新 CountsEnds7、SourceBindings4、GuardBinding2、
ProposalBinding2、round、$I^*$。它不是重写原回应状态。
M 仍为九 B域、实际 $U(d_{cat})$、恰 $d_{cat}$ 个5域项、全预算耗尽：

| 固定域 | 完整载荷 |
| --- | --- |
| 1–4 | 当前已装 stage settlement版本；实际 $I^*$；实际 Q原引用键；实际 DA原引用键 |
| 5–6 | 完整原 canonical三引用字；实际原 c |
| 7–8 | 旧 CountsEnds7；真正检查后的新 CountsEnds7 |
| 9 | 完整实际释放 Y |

CountsEnds7 仍为 $T_7(q,g_c,e,j,m,semantic\text{-}endOption,unified\text{-}endOption)$。
M 的 Q／DA键必须命中 catalogue 的实际载荷项，并不是 AA访问 Native端口的能力。
A以真实字库装配／测量导出／封存后，才发送 $U(|M|)$、整个 M 和010。

**定义 21.2（AA实际接收与绑定选择）。** AA 处于本 attempt 的 delivered／AwaitSettlement。
逐位接收 unary length并真实写 length-marks，按 marks逐位 backing body，再完整接收010。
ending完成前 body不可作为可用完整字解析。
实际 ReadAAFrame逐位读长度、分配／消耗 marks、复制 payload；
先九次，再实际 unary catalogue count，再每项五次，最后预算耗尽。
每个 bit／next／cursor／budget 都有真实字段，缺位、多位、坏结束走局部 fault。

全比较 $I^*$、实际 Q／DA／transport 元数据／PayloadACK／Confirmation与 retained attempt；
完整 canonical header／length／payload、operation／stage／RBC、$S_w$、receipt、$G_i$、
guard／proposal／round、旧／新 CountsEnds7、J15／U18、semantic mate、两个各自前驱、
全部 before／after（包括 accepted-Rho e）、manifest、两个实际六域 fence、boot／prior／身份。
manifest按实际 count及各tag元数全读；栅栏真实性来自真实 writer和连接归纳，
不把数值相等当 meter 读数或权限。

绑定前检查实际用到的三个已装驱动器 Ready及当前所需 grants。
C1 时 $N^*$仍 fresh；C2准备前检查它仍 fresh，候选完成后为 spent／Ready。
C1分配 $B_1$，逐域写 none previous-binding、$O,F,N^*$真实上下文、
$Q_1$/outbox1、实收 $M_1,Y_1,J_1,U_1$、完整 dependency backing 和 outcome。
全部字段seal后才更新 choice和 tail；实际 $Y_1=1$ 选F，否则选O。
C2先全查实际旧 $B_1$/receipt，分配 $B_2$，保留三个上下文及真实 $B_1$ 引用，
再写 $Q_2$/outbox2、$M_2,Y_2,J_2,U_2$/backing并seal。
实际 $Y_2=1$ 才选 $N^*$，否则保留 $B_1$所选旧根。
两次选择都不写根槽、源边、权限或历史，也不把同名新分配物当已有驱动器根。

**定义 21.3（完整 ACK、Done 与捕获状态重载）。** binding seal／selection／tail 后，
AA构造真实

$$
ACK=T_4(\mathtt{NSACK3},I^*,\text{整个实际实收M},\text{实际outcome}),
$$

干计数其封存 backing，打印全 $U(|ACK|)$、body、010。
A在74分别实测分配 length、body、ending块及各自29 descriptor，body在ending检查前status0。
长度逐位 IN5／EX74／WR74(5)／RD74(4)／MR74至真实0；
body用完整计数字逐位 RD计数／IN5／WR74(5)／MR74／MR计数，末尾 RD0；
ending三位各执行 IN5／EX74／WR74(5)／MR74／ML74／RD74(4)／MR74，
保存此前失配位并接收全三位后分支。
全部匹配才重载 descriptor／写body status1，坏ending保留status0。

然后预算 ReadFrame恰四次并耗尽，逐位及两端比较 NSACK3、完整 $I^*$、整个 M、恰一位 outcome，
后者必须等于真正返回Y。重查 Wait、捕获的新状态handle、packet、c和两端点。
通过才封存 Done8：stage版本、wait-ref、M-ref、ACK-length/body/ending三引用、
捕获的新回应状态-ref、实查 choice。ACK echo不是长度或一枚结果位。
C1的不可变 receipt-carrier此时才由已完成 M／ACK／Done构造。

74入口按定义2.6保存保护头距离及是否R；结束恢复普通头，原R约定恢复到新Tail74。
同一companion原区间和status不改，carrier也与scratch分离。
再新 Close29，在包含所需对象的界内重载**同一个被捕获的新回应状态**，
不采用 helper留下的旧 LatestType 状态。
只有此时进入一条原 AfterFinal，读真正Y更新参考 t／叶对／consumer stage，
测量导出并seal原完成轮状态25，十二反向TOK回P、规范角色、实际Tail13／17及原Entry。
C1后的下一 loan／reload／Select 才构造 Right或Rho及下一独立GuardIngress；
C2后原stage选择 Handback，没有第三次原子attempt或下一guard接收。

**引理 21.4（结算与真正下一消费者）。** 在假设13.2及第19–20节真实返回下，
两次结算有限完成，AA选择各等于真实Y所指定的已装根，完整ACK后才启用原下一入口。

证明。固定有限29界上的 full-key去重使可能新键有限，typed表保证每个实际解引用字段有完整载荷，
没有沿origin反向追 unavailable外物。九／count／五域的真实发送接收前缀归纳给出AA实收M；
它与早先真实attempt／transport及原行全比较通过。
每个绑定域有实际早先来源，seal先于成为当前；选择不改变driver授权。
ACK用整个实收M，逐位backing不变量给出A恰收到该字，四域／echo／Wait检查后Done才存在。
引理2.6及原RG6.2的全池／状态／Entry边因此在同一真实配置适用。
局部AA ACK、PayloadACK、copy TOK和whole-row ACK均有别的方向／阶段／语法，不能替代这次结算ACK。
C1回应及真实旧回执遂成为C2的实际前驱。$\square$

## 22. 原 Handback、Stop 与 INITIAL 的完整消费

**定义 22.1（共同终止入口）。** 最后ACK的ending被A完整消费并backing后，
supervisor经已装边进入 FinalPark，保留 $B_1,B_2$、三根、所有历史、attempt、outbox、M／ACK及连接。
三个驱动器均Ready且无pending request，不再编辑或发布。
此 parking在原Handback及global halt之前发生，不能在halt之后补做。

第二次原AfterFinal完成的Entry上，P持全十二字，dispatcher持源服务token，
RG持原invocation，A持24–31／64–74及其保护权；
最新真实返回／完成状态、两journal端存在，原表24和启动时保存的原25／27／头数据仍存在。
因此原finish分支先借池／reload选择结束，在A持池时导出并seal HandbackPending，
归还全池、CTL到Handback，再重新借池／reload；不在A已持池时再发起一次loan。

**定义 22.2（原配置与真正 Stop）。** 按实际本地引用／descriptor／status解析保存的原配置、
waiting和表绑定，用其**原配置／栈语法**执行 CAP8.1、ARC28.1的完整逐字复制，
在25追加fresh active original configuration，在27追加其初始空waiting，
全部原引用字段、实测base／length／descriptor／status完成后才装为当前。
保留所有RG／AA状态、旧source、journal、archive；这不是source或历史rollback。

按原定位程序置表24，归还全十二字，恒等角色CTL、实际Tail13／17，
一次TOK将RG invocation归还原client槽，再原十二字loan和entryCTL。
不变原解释器实际读自己的表及新active原配置，执行真实Stop，在31写出／seal $(0,B,1)$。
原terminal output／packet、原instruction／control依赖均经49完整到P21，
在Halt承诺之前完成其真实descriptor／origin／seal。
RG Native描述不被当作原Turing表。

**定义 22.3（Halt、snapshot、verifier和最终输出）。** 原Halt执行实际start／commit、
原semantic／unified行及依赖，48完整交付，两个joined ends全查，最后whole-row ACK。
冻结包括Halt的完整index19／18：实际扫描构造 $m_*,j_*$，保留并比较两个各自last-reference。
构造／封存真正 SEG-P1 snapshot-index及其逐项 request／semantic-mate绑定，
完整列出原boot／initialization／prior、所有请求、control、output、J／U材料。
每个需要块经50的真实allocation／mailbox／copy／status／seal到verifier32／33，
origin解析只使用它已取得的本地副本；没有原子多带freeze或自由snapshot导入。

原verifier在 $H_0=1$枚举全部 $4^{2H_0-1}$初始包，完整验证包和实际prior
$\{\alpha,\beta\}$，分别保留初始target和replay-current状态。
按实际冻结顺序全读每个U及其J／request／control／output：
历史Reserve／Raise的比较、布局及manifest，source event在各自历史h的完整操作及回应，
每次 $q,g_c,e,j,m$ 更新、两个独立前驱、code、fence和terminal-return-kind均按CAP6.5执行。
不得只读最新guard或把source-free F7／字工作伪造成NativeLocal行。
目标比较始终是原初始 $q_1$，不是当前树的新目标。

实际seed beta的旧取得前缀排除初始alpha；后续真实原事件由命题19.5及第20节供应，
CAP6.6的逐行归纳保留实际初始beta。兼容initial fiber因而非空且对INITIAL-$q_1$恒定。
原verifier真实构造已接受的 SEG-R1，类型 INITIAL-$q_1(\beta)$。
receipt的creation／seal来自完成的真实delivery descriptor，不预写自身未来seal-fence数值。

按CAP6.5，原expected-task／proposal／frozen-prefix／snapshot binding真实构造并复制到consumer40／41；
实际receipt完整经51交付及seal。consumer逐字段解析并比较原 $\xi,H_0,prior$、
proposal、type、两journal counts／两ends、snapshot及真实accepted receipt seal，
才Zero-allocate43、逐位复制target、seal并执行要求的逐bit OUT。
完成实际acknowledgement、全部规定token归还，最后global-halt CTL。
没有以AA成功token替代SEG-R1，也没有以receipt名称替代target实际输出。

**定理 22.4（同一次准备上的原终止消费）。** 在假设13.2下，若第二次真实结算和
原完成C2 Entry按上述构造达到，则定义22.1–22.3在同一 $\xi$ 上有限完成，
实际输出原Stop提案 $(0,B,1)$ 所绑定的INITIAL-$q_1(\beta)$结果并进入吸收global halt，
只发生一次final handback。

证明。保存原配置先于任何RG append，旧字不可变；第二次完整返回／ACK／state reload
供应定义22.1的同一owners、tokens、invocation和配置，故RG9.1的真实入口成立。
新active原配置的完整复制、表定位及workspace／invocation转交供应原解释器入口；
原Stop及其output/control材料实际到达P后，CAP6.3的Halt／snapshot路线可执行。
原seed排除alpha、真实beta在全部authentic rows中存活，CAP6.5–6.6的
历史guard verifier及其初始target判据给出真正accepted receipt。
完整expected binding和receipt复制／consumer比较把该值接到实际43输出，
RG9.2的ACK／token／halt尾部遂在此共同配置适用。
唯一finish边把invocation移出RG，没有回传边；吸收halt无后继。
所以不需要源一直保持beta，不重置源，也不能在halt后重新进入该消费者。$\square$

## 23. 全部有限守卫域的两阶段接合定理

**定义 23.1（真实 C2 ingress 与四类尺寸）。** 引理21.4的C1退出后，
原Select读真实Y：拒绝时构造Right$(\alpha)$，接受时构造Rho，先封存proposal，后GuardIngress。
按RG5.1在A69实际Base后逐位 IN／EX／WR／RD-test／MR，
直到独立供应 $U(g)$ 的终止0；写sep／status0及实际十域descriptor，At／WR1／CTL后新Close29，
完整取得本块，parse恰一个unary并耗尽，检查 $g\ge$实际上一参考guard。
实际 $G_i$ 绑定本次guard-ref、proposal-origin、round及preceding selected-final。
这些动作对长guard全部执行，未用阈值字替代输入。

C1的原参考candidate是 $\langle D,D\rangle$，有4叶、weight10。
其两个真实结果和后续C2的全部有限域如下：

| 阶段／已取得条件 | 原完整维护 | 实际 $h=K$ | $N$ | $c_{\rm cap}$ | $L$ | $W$ | 候选叶／活跃token／PAD | STORE数 | 真实Y／AA选择 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| C1 guard2，Left | 无 | 5 | 9 | 19 | 38 | 54 | 10／19／0 | 18 | 0／O |
| C1 guard4，Left | Reserve10、Raise10 | 10 | 19 | 29 | 58 | 94 | 10／19／10 | 38 | 1／F |
| C2 after C1 guard2，$g=2$，Right | 无 | 5 | 9 | 13 | 26 | 48 | 7／13／0 | 18 | 0／O |
| C2 after C1 guard2，所有有限 $g\ge3$，Right | Reserve7、Raise7 | 7 | 13 | 17 | 34 | 64 | 7／13／4 | 26 | 1／$N^*$ |
| C2 after C1 guard4，$g=4,5$，Rho | 无 | 10 | 19 | 57 | 114 | 122 | 16／31／26 | 38 | 0／F |
| C2 after C1 guard4，所有有限 $g\ge6$，Rho | Reserve16、Raise16 | 16 | 31 | 93 | 186 | 194 | 16／31／62 | 62 | 1／$N^*$ |

每个表中维护都执行原完整call／记录／ACK／token／idle／return／state安装。
Right参考candidate三叶、weight7；Rho参考candidate六叶、weight16。
原Plan的阈值分别3、6，其accept分支要求实际严格Reserve／Raise到7或16，
各保持selected source／reference t而扩展真实布局与unified谱系。
Rho两行的d／M／T均不存在，第7域是本次新marker-reference；
Right两行有真实 $D,d=2,M=3$；C1两行有真实 $C,d=5,M=9$。

**定理 23.2（JCOMP2-OI-F7C1的完整有限域）。** 在假设13.2下，存在第13–22节给出的
一个固定有限原始安装 $J^*$，对定义13.1的每个实际完整输入序列，
它自身两种C1备选运行及各自所有完整有限C2守卫均有限完成：
自己的真正C1原子供应、完整原返回／第一次结算／全ACK／捕获新状态重载；
原回应驱动的C2构造及实际独立guard取得、全部维护、真正C2 Right或Rho原子供应；
完整原返回／第二次结算／全ACK／捕获新状态重载；原AfterFinal／Entry及定义22.1–22.3的
Handback／Stop／Halt／INITIAL验证／receipt／consumer实际输出／ACK／token归还／global halt。
全部沿同一个原准备发生 $\xi$，所有mandatory接口有实际writer和完整reader。
其源回应、原行语法／双前驱／原消费者意义按各自原合同成立，所有新增资源由第24节同次运行递推计费。

证明。采用以下阶段不变量：指定最终wait处Native源等于由真正RG状态算得的 $E(t)$；
实际post-maintenance $h,K$、manifest、计数和两端点存在；AA的已选旧根内容也等于此字；
只有一个attempt活跃，候选根distinct／fresh，call／guard／receipt／start-fence等均有此前真实writer。
内层每次Return恢复AA真实history／tape不变量；外层每bit满足backing／status不变量；
forest／frame／BANK地址和STORE-prefix满足第18–19节不变量。
真正返回seal后才结算，完整ACK后仍重载同一捕获新状态，binding选择仅由真正Y决定。

定义14.3和引理14.4由自己的boot／seed／Lift／C0及真实C1维护建立基例。
C1用自己的F重放及八项编辑产生完整候选；第17–18节的graft writer／reader，
第19节实际运输／全程序／release和第20节原记录／return供应真正 $Y_1$。
第21节第一次结算供应 $B_1$、全ACK、Done／carrier和原下一Entry，
因此C2不是从旧J的已到达对象或假定下一Ready开始。

C1 refusal时参考t仍D，Select构造Right(alpha)；accept时参考t为$\langle D,D\rangle$，Select构造Rho。
定义23.1的真实独立receiver／新界／完整 $G_i$建立本次guard谱系。
由RG7.1的实际Plan计算，Right的参考叶阈值3／encoded目标7、Rho的阈值6／encoded目标16
给出表中恰两类整数区间；维护全返回后仍保持相同selected source和t。
所以本次状态见证及实际 $M_1,ACK_1,Done$/carrier可取得，旧根Tag检查与B1回执检查通过。

引理16.3或16.5在自己的fresh N根上产生整体Right或Rho候选。
第7域的两个typed分支及全部28／8／10完整扫描供应真实新BIND，
Rho不通过旧强制T规则进入，也不制造context。
第19节由实际bank消费完整候选；完整parser在表列h上给出真正Y，而非Plan赋值。
C1的拒绝行及C2的两个拒绝区间均为真正executed refusal，所有STORE／response-tail／rows仍完成。
特别地accepted C2 Rho在第20节选本次e-plus，使原J／U和随后verifier的计数关系一致。

两条前驱、完整依赖、whole-row ACK／source TOK／idle及新的返回state再次由第20节取得，
第二次M／binding／全ACK／捕获state reload由第21节取得。
故C2完成Entry与AA停车、全部owners／tokens／invocation／保存配置／两端点是同一实际配置。
定理22.4在其真实入口适用，给出完整原终止消费。

有限性也沿同一出口逐段组合：新Native控制只由Raw、完整有界parse、有限字／列表运算、
typed origin scan、unary算术及固定stage／port case展开；AA只由实际分配、逐域操作、测试、
IN／OUT、ACK和有限phase展开。Fetch实际停止于有限history的OutOfRange；
树遍历有限，旧frontier编辑前封存；forest孩子严格更早，FEND固定Q，catalogue新键在有限闭合界内。
八／十／28固定分支各有限，扫描期间不append其源界，保存后才扩展。
每个有限g提供有限完整guard字、描述符、比较和records；不需一个跨g最大值。
串行连接在对应receiver已到位时逐位发送，backing后再下一位，ACK只依赖已完成输入，无未来数据的等待环。
原prior／controller终止、完整输入及材料按假设13.2保留，遂有全程逐点有限完成。$\square$

**命题 23.3（量词不由尺寸饱和缩小）。** 四个C2区间穷尽两种C1后分别所有
$g\ge2$、$g\ge4$的完整有限输入。尺寸在阈值后相同，不使guard、发生、引用、扫描或费用恒定。

证明。Right把整数域分成2和至少3；Rho分成4、5和至少6。
原receiver对每个实际 $U(g)$都消费其 $g+1$位，包括终止0，
之后实际Base／length／descriptor／status、单调比较、G_i／proposal绑定及state／record字均按该字生成。
后续prefix长度和ordinal也取真实新值，不能把该日程替换为两枚阈值fixture。$\square$

## 24. 真正新出口上的全程资源递推与精确子计数

**定义 24.1（同次运行的向量与峰值）。** 把定理23.2的完整日程依引用原过程展开到
实际Native原语和AA逐域／分配／I-O／ACK／控制转移。
保留定义11.1的独立坐标：按owner／purpose／opcode的Native次数、ticks、fees、receipts，
普通构造格、有限代码／控制／类型／token／连接物质、全部定位／头移动、每方向wire位，
完整descriptor／unary／reference表示；AA另有真实分配、字段读写、测试、I-O、局部ACK、
控制和实际引用存储。两类工作不以一个任意标量汇率合并。

对实际相继原语 $e:z\longrightarrow z'$ 定义

$$
V(z)=\chi(e,z,z')+V(z'),\qquad
P(z)=\max\{S(z),P(z')\};\qquad
V(z_{halt})=0,\quad P(z_{halt})=S(z_{halt}).
$$

$S(z)$包括全部仍保留材料；组合为
$V(A;B,z)=V(A,z)+V(B,\operatorname{exit}(A,z))$，peak取实际连续前缀最大值。
每个后段的入口是前段本次**新实际出口**。fence readout只读已封闭cut，
读数自身后续receipt仍计入当前meter；不解自包含读数方程。
没有完成输入时只有已执行前缀账，没有成功halt总量。

**定义 24.2（全程逐段展开）。** 递推的顺序段包含下列全部工作，各段中的完整原过程按其
实际字段、地址、头、状态和返回边展开，不赋服务常数：

| 顺序段 | 必计的实际内容 |
| --- | --- |
| 安装／共同boot | 原及新增字面row／code／control／全部type和21种F7C1 type／root-slot／token／全部连接；$\mathscr D^*,I^*$实际写入与复制；三根allocation／初始化、O七次完整编辑及boot-done |
| 自己的Native前缀 | beta ingress／完整验证、源布局／counter／directory／boot／prior／seed；原Stop保存配置／表／头、mode／invocation；Lift、C0、C1实际维护及全部原记录／返回 |
| C1准备 | 完整state reload、$S_w$计算／导出、initial receipt、Companion20及packet两个完整49通道与全池转交；canonical／原conversion、F7Stage／holder、旧值／五预备增量、manifest／唯一source-start、Attempt／Q24 |
| C1供应／程序 | O Tag／Fetch／F真实重放／八编辑／所有祖先Maintain／新Tag／outbox；五外层帧的逐bit打印／backing／检查／ACK／Confirmation、bank／DA；新版Input22／所有全reparse／nested检查／快照／BIND、forest／FEND／frames／results／Resolve／code／解释／全部STORE／cleanup／release／commit-fence |
| C1返回／结算 | 真正Y选counter、J／U／indices／sidecar、所有48依赖／checks／全池／whole-row ACK／source TOK／idle；ComputedReturned／新state；新界／Wait／catalogue／M、AA binding／全ACK、A74 length／body／ending／status／全echo／Done／carrier／捕获state reload／原AfterFinal／Entry／Select |
| C2独立输入／维护 | 每个实际 $g+1$ guard位的IN／WR／测试／移动／sep／descriptor／status／新界／完整导入／单调比较／G_i／state／Plan；每个实际Reserve／Raise的完整调用、布局、两链、依赖、ACK／token／idle／返回 |
| C2准备／真实候选 | 新 $S_w$、实际carrier／$M_1,ACK_1,Done$取得、Companion20／packet／Q；selected-old全Tag；DN全部replay／Right lift或旧frontier acquisition／Rho edits、全部祖先维护、记录／路径／引用、最终Tag／outbox；本次F7 writer／holder及完整读取 |
| C2程序／返回／结算 | 第二次全部transport／bank／DA／Input22／28-8-10全扫描／BIND／forest／code／解释／全部STORE／cleanup／release；operation-dependent counters／J／U／依赖／完整return；第二M／binding／全ACK／Done／捕获state reload／AfterFinal／Entry |
| 原终止消费 | AA FinalPark；finish／Handback两次不同loan／完整原配置复制／表定位／invocation转交；原Stop计算及全部49 terminal／control／output材料；Halt全行／依赖／ACK、双端freeze／SEG-P1／expected binding／所有50复制／完整finite verifier／receipt／所有51复制／consumer全检查／43复制seal／逐bit OUT／ACK／token／halt |

所有Raw、tuple、Append22、Lookup、origin／type／ordinal扫描、完整比较、角色CTL、失败测试、
At／Last／Home／Tail、status、seal和每个TOK都属于实际展开，不因“辅助”或“已知相等”而免费。
AA链项实际先写bit／next=null、再链接head／tail；历史重放查询、Tag回复、请求、Growth、
End／ACK／Return、header／tape维护及每个祖先／引用实际长度均计入。

**定义 24.3（字段、门、线与复制的精确项）。** 设 $r_7$八个实际组件为 $a_1,\ldots,a_8$，
Input22实际28字段为 $f_1,\ldots,f_{28}$。则

$$
|r_7|=\sum_{i=1}^8(2|a_i|+1),\qquad
|Input22|=\sum_{j=1}^{28}(2|f_j|+1),\qquad
|B(r_7)|=2|r_7|+1.
$$

graft referent payload为 $2M$位；Rho marker的P21 payload／sep／status恰3格，
这不含descriptor、字库、引用或type/control。
holder payload／sep／status为 $|r_7|+2$个P77格，
P27-field7快照及decoded field7快照也各为 $|r_7|+2$格并各有自己的descriptor／reference。
八个component快照、所有临时字／长度字及退役版本均保留计费。

一次Raw包含Base、完整干长度、FieldBody、sep／status0、distinct-output Add、
十域准备、完整descriptor计数／ordinal／write／seal、At／WR1／CTL、
八域reference构造／Copy／role permutation、Tail目标／17。
一次 $T_r$父构造包含全部字段取得／Raw77快照、New11、每次preserving Reload／Frame、
Finish／Copy及完整Raw目标。每个component保存也先付全源扫描，再付自己的Raw。
外层28遍每遍消费全部28域，所以第7个frame实际被读28次；另有八次完整 $r_7$ reparse、
holder查找和全字比较、十次完整descriptor组件扫描、真实unary arithmetic、status／range检查及payload验证。
不把它们折为28次单位lookup，不添加不存在的marker／Input22公有copy或catalogue-entry费用。

对每个实际门保留定义11.3／PR57.06的四个新地址 $v=(a,b,c,d)$ 和实际seek前头 $h_{G,r}$：

$$
I(G)=18+5\sum_{r=1}^4(v_r+1)
       +\sum_{r=1}^4(2h_{G,r}+3v_r+3)+5+P_G.
$$

$P_G$展开到本次缓存descriptor、seek、Home／Last／At、status／control，
不是未定义服务费。terminal RD／exit、generation、allocation、cleanup、response、行和return另计。
原行全长仍为 $\sum_{s=1}^{15}(2|J_s|+1)$、$\sum_{s=1}^{18}(2|U_s|+1)$。

令本次 $q_Q=|Q24|$，五帧wire长度恰为

$$
2q_Q+8,\quad2q_Q+8,\quad2q_Q+c_{\rm cap}+2L+10,\quad
2q_Q+L+9,\quad2q_Q+L+9,
$$

总计 $10q_Q+c_{\rm cap}+4L+44$；两端打印／接收／backing／全解析／echo／状态及AA工作另计。
C2 receipt完整内嵌可显著增大Q，不能沿用C1的q数值。
若M固定九域为 $u_s$，catalogue条目为 $w_{t,s}$，则

$$
\ell_M=\sum_{s=1}^{9}(2|u_s|+1)+(d_{cat}+1)
 +\sum_{t=1}^{d_{cat}}\sum_{s=1}^{5}(2|w_{t,s}|+1).
$$

M wire为 $2\ell_M+4$，Native send核心为 $8\ell_M+13$；
ACK长 $a$ 时wire为 $2a+4$，Native receive核心为 $10a+27$。
所有allocation、position、descriptor／seal、完整四域parse／全M echo和AA工作另计。
每个实际48／49长度 $k$复制保留两循环／seal／TOK核心 $12k+6$、四次全池handoff的52原语，
再加全部setup／Base／Zero／status／descriptor／position／检查。
whole-row ACK／source TOK／idle另计；50／51／receipt／output采用其原完整展开计入终止段。

**命题 24.4（实际成功增长与源顶点子计数）。** 三根的成功增长和最终源顶点有下列精确子计数：

| 根／路径 | P次数 | S次数 | 成功增长总数 | 含物质unary marker的最终source顶点 |
| --- | --- | --- | --- | --- |
| O | 3 | 4 | 7 | 12 |
| F | 6 | 9 | 15 | 25 |
| $N^*$ Right | 4 | 6 | 10 | 17 |
| $N^*$ Rho | 10 | 15 | 25 | 41 |
| 三根合计，Right运行 | 13 | 19 | 32 | 54 |
| 三根合计，Rho运行 | 19 | 28 | 47 | 78 |

证明。O七项及F七项重放／八项编辑直接给前两行；引理16.3、16.5给后两根行。
每根初始顶点1，P新增一个marker，S在复用旧marker为左beta时新增其marker和右alpha共2顶点，
故实际顶点数为 $1+\#P+2\#S$。三根distinct，合计相加。
这些数不含headers、tapes、drivers、queries、请求／回复／handshake、辅助records、引用和任何Native工作，
不是总工作、峰值存储或最小性结论。$\square$

**定理 24.5（完整逐点费用及非恒定几何）。** 在假设13.2及定理23.2每个完整有限输入上，
定义24.1–24.3对第24.2表全部顺序段给出有限的每一可加坐标和同次运行存储peak。
若实际Native原语数为 $n_N$，receipts／ticks／fees恰为 $n_N,n_N,2n_N$。

证明。定理23.2给出有限原语展开；每次分配／写入有有限完整表示。
$S(z)$保留O／F／N源、header／tape、所有原archive／STORE／退役bank／state／program／descriptor／counter／index，
两次attempt／outbox／settlement／binding／ACK、carrier／witness／Companion、F7 holder／marker／快照，
以及全部连接／partial buffer、原terminal snapshot／replica／receipt／output。
Native普通格／receipt仍按定义11.3的 $S_0+b_{control}+8A_N+8n_N$，新增control／type／token等明计；
AA独立物质不隐含在该式。清零不退还已构造格。
有限执行上的向量求和及存储最大值因而有限，原每原语一receipt／tick、两fee给所列关系。

较早第三根、control／type、F7字／holder／快照、完整guard、carrier和检查会改变后续
arena base、unary address长度、local ordinal、fence、catalogue及scan长度，
$\mathscr D^*,I^*$及Q／M／ACK字长也据本次生成。
因此每个后项必须在前项真实新出口求值，不是把旧J总量加常数；
更不能从一个未定义的旧Rho字段日程减去所谓旧费用。
本定理是source-model递推和上述精确子计数，不是实测整段数字总量；
跨g统一硬件／时间界、资源优势或最优性均不由有限性推出。$\square$

## 25. 钉版来源、已供给部分与保留的全局边界

**定义 25.1（原结果的准确复用）。** 下列 primary source 均固定在
`958bf687adefa26ca85a4d2894d3189a5f86720c`，引用指向该快照的原文及具体条目。
它们供应的前提／结论只在表列范围使用，不以当前其他几何或通用context提案补桥。

| 来源与精确条目 | 本增补的参数对应／用途 |
| --- | --- |
| [AS1.3–2.6、3.1–5.5](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION.md#L47-L594) | 第14–18节复用有限安装、先行描述／身份、Raw／pack／十二字、真实C1历史及运输；原强制T仅作为graft来源，新的Rho字段由第17–18节实际供应 |
| [AS6.1–9.6、11.1–12.2](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION.md#L596-L1409) | 第19–24节复用原生record／forest／frame／Emit、全部parser／MUX／STORE／release、原行／新state／typed closure／全ACK及费用算法；operation、e-plus、stage和新版Input22按本增补参数化 |
| [AA17.1–17.3](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#L1014-L1105)；[AA19.1–20.3](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#L1262-L1485) | 三个alpha出生实际根各有独立driver／rights；第16节按出生类型复用合法history和tape recall，逐项走真实Navigate／Maintain／End／ACK／Return；只使用非Next的完整服务结论 |
| [LAB9.3–9.4](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md#L853-L923) | 第16.4–16.5节对实际非alpha可达 $\langle C,C\rangle$复用stationary旧叶frontier的结构论证；不据此取得未装控制器、Tag对象引用或graft权限 |
| [RG1.1–3.3](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md#L11-L266)；[RG5.1–9.2](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md#L364-L818) | 自己的beta／seed／保存配置／invocation、每次新闭合界、独立全guard、真实returned-state／Entry、原Plan阈值、response-dependent C2和最后一次Handback |
| [CAP4.3–4.6](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md#L507-L708)；[CAP6.1–6.2b](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md#L864-L1442) | 每个S的实际Resolve、raw写入单射、原canonical三块、accepted-Rho e、八域reference／十域descriptor／真实status／origin、固定预算parse、真实fence与J／U双链 |
| [CAP6.3–6.7](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md#L1517-L1868) | 所有实际copy／ACK／token、包括Halt的双端snapshot、原历史guard verifier、expected-task binding、INITIAL非空恒定fiber、receipt／consumer／OUT；仅在第22节共同入口已证后应用 |
| [PR57.D4、L3、D5、T1–T2及.06–.10](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#L18145-L18252) | 有限literal gate生成／解释、全部unused算术臂／carry、whole-candidate parser／MUX、graft容量 $1+N+M$ 与Rho容量 $3N$；不把被删scatter当仍执行的前提 |
| [ARC16.2](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md#L2135-L2155)；[ARC26.2–27.2](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md#L3583-L3792)；[RCA12.1](https://github.com/the-omega-institute/trureturing/blob/958bf687adefa26ca85a4d2894d3189a5f86720c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md#L1186-L1221) | 实际有限字／list／unary运算、测量导出／保护头导入／闭合界、原packet send／完整return；变量列表并非无限控制状态或单位成本字典 |

本增补的仓内新增综合是：同一次新boot上，两阶段的selected-source、actual-operation、
真实receipt／return与原terminal consumer的有价连接；尤其强制第7域的操作索引writer／holder／
完整reader／BIND接合及其局部／公有依赖边界。
历史重建、出生类型、旧frontier替换、字算法、parser、gate执行和原verifier方法均沿用表列来源，
不将其整段重证计为新内容。本增补未完成外部文献穷尽检索，不主张全球原创性。
其证据级别为带明确前提的普通source-model构造与归纳，不是Lean／kernel、装置运行或实测费用证明。

**命题 25.2（对旧定义12.2的精确限定）。** 定理23.2供应旧定义12.2中下列有界部分：
一个新原始安装、它自己的两种C1真实分支、其后所有所声明完整有限guard、
恰一个先前未用第三speculative根支持的response-dependent C2 Right／Rho，以及实际完整原Stop／INITIAL消费者。
因此本增补的结束点是原global halt，不再只是C1后的下一构造。
原定义12.2及第1–12节的字节和原定理各自范围保持原样。

证明。引理14.4建立自己C1，第21节建立真实C1后的原Select，第23.1–23.3覆盖全部所声明g，
第16–20节构造自己的第三根／字段／程序／原行／return，第22节供应完整原终止。
这些存在量词都绑定在同一个新 $J^*$和同一次输入运行上；不对已经到达的旧J作安装动作。
没有从内容对应推出旧微迹、旧引用、旧费用或完整公开镜像相等。$\square$

**定义 25.3（仍未由此给出的结论）。** 第25.2的限定不提供整个supplier族的任意替换，
不提供任意Busy／内部／all-cut current acquisition，也不提供四个可独立使用表达的全部原消费者，
original-Q新增行／cross-entry／全terminal kernel或通用恢复核。
它不把已用 $O,F,N^*$根重新当fresh资源，不供应固定旧J上的任意后来原子stage或任意串行新权限。
它不扩大为一般alpha／beta实际操作桥，不借用未建立的generic-context或其他新几何关系。
原INITIAL目标仍是唯一原准备的目标；没有后halt reentry、任意later terminal task或当前目标转换。
物理实现、统一有限设备容量／时间、资源优势、全资源比较及global／Pareto最小性仍在结论之外。
第24节是同次运行的完整递推及明确子计数，不赋予数字整段实测总量，
也不把此有限单元当作更大RRO目标的完成。

## 追加锚（本行以下为增补区）

## 26. 单次原始启动上的完整普通有限族

**定义 26.1（原消费者、树及输入域）。** 第26–40节给出源模型安装
`J-FAMILY-ARENA-1`。消费者是 RG 定义1.2、4.1–4.2、5.1、6.1–6.2、7.1、9.1
的原 RG2 mode01：原 Select 实际接收 repeat／finish；repeat 后由原 raw receiver
取得尚未知的修改请求，完整返回其真实 staging refusal，再独立接收参考守卫，
执行原 Plan、原 computed calls、完整回应安装及下一 Entry。
这里没有另设命令列表解释器。数学来源一律取第40节所列固定快照。

树语法、左右次序、原七服务、当前权限、完整回应及原任务沿用定义1.1及 CAP1.2。
为避免与轮数混淆，本增补把原生成器的 $N=2h-1$ 记作 $N_s$，不改原字段的意义。
设

$$
\begin{aligned}
\rho(\alpha)&=\beta,&\rho(\beta)&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle,\\
E(t)&=\rho^2(t),&n(t)&=a(t)+b(t),&w(t)&=2a(t)+3b(t)=n(E(t)),\\
c_{\mathrm{Rho}}(t)&=\rho t,&c_{\mathrm{Left}(v)}(t)&=\langle v,t\rangle,&
c_{\mathrm{Right}(v)}(t)&=\langle t,v\rangle.
\end{aligned}
$$

$E$ 是树映射，与原 ReadE 的 Clifford 值分开。Native 前序令牌为
PAIR11、alpha01、beta10、PAD00；AA Tag 的四值编码仍为 alpha00、beta01、branch10、absent11。
物质 unary marker 既不是逻辑叶，也不在逻辑编辑地址中。

安装先于任意未来轮数、操作数、守卫及结束时刻。完整普通域量化为：每个有限 $N\ge0$，
实际先后供应的 $A_i\in\{\mathrm{Rho},\mathrm{Left}(v_i),\mathrm{Right}(v_i)\}$，
graft 的每个 $v_i$ 为在原 raw ingress 实际收到的任意非空有限有序树，
另在各原 GuardIngress 独立供应有限 $1=g_0\le g_1\le\cdots\le g_N$，
最后实际供应 finish。选择允许依赖已经真正取得的先前完整回应；未来选择不进入安装参数。
从 $t_0=\beta$ 定义

$$
\varepsilon_i=[n(c_{A_i}(t_{i-1}))\le g_i],\qquad
t_i=\begin{cases}c_{A_i}(t_{i-1}),&\varepsilon_i=1,\\t_{i-1},&\varepsilon_i=0.\end{cases}
$$

待证对应是每个完成 Entry 的原源16为 $E(t_i)$、实际 $h=K=w(t_i)$，
且所选真实 arena 子树具有该有序 body。源身份、parent、历史和费用不由 body 相等而认同。

**假设 26.2（逐点完成条件）。** 采用假设1.2、13.2及 AA20.1 的理想顺序原语，
CAP 的所有权／布局／描述符／栅栏／通道合同，ARC／RCA 的有限字及双库程序，RG 的原始入口和返回。
本次完整运行所需的实际有限新材料、工作存储、完整原 ingress 和规定确认均供应；
实际到达的原 prior／controller 计算终止；源、记录、端口、连接的所需权限始终当前独占有效，
没有竞争写者、撤权、崩溃或中断。连接只允许绑定 sender 在空时 OUT，
receiver 对该位 IN 并完成规定 backing 后才开放下一位。

这些是每个具体有限执行的条件，没有跨 $N$、树大小、守卫或历史的统一有限容量。
不增加名为 Import、Bind、Ready、Return 的原语或进展公理。
AA 的 Ready／Return 是 AA20.2 的实际阶段／边，BIND 是后文实际写出的记录。
缺输入的执行只具有真实已到达前缀，不据此承诺 terminal。

**定义 26.3（保留的另一分支）。** mode10 仅保留定义13.1、23.1及定理23.2的原域：
C0 guard2；C1 guard2 或 guard4；C1 完整结算、原 AfterFinal／Entry／Select 后才接收
任意有限 C2 guard，分别至少2或至少4；原真实 C1 回应决定 C2 为 Right(alpha) 或 Rho。
它使用原 $O,F,N^*$ 三固定根及原算法。mode00、11保留各自原 raw／局部退出边。
TMC PR57.D5／T5 的 fixed-H 有效内部策略、CAP8 的 safe-growth controller、
本节外部独立守卫和上述固定 mode10 是各自的合同，不把其输入权力并成一个新策略域。

## 27. 四个真实根、有限控制与先行身份

**定义 27.1（实际载体）。** 保留 RG 的0–73端口／所有者、定义14.1的 A74及 P75／76／77。
P16 是私有源／work，P17 是描述符，P21 是完整 staging，P22 先存 Input22，再从另测起点写 forest；
A29、A64–68 保持原描述符／字库语法。工作池恰为端口1–12。
16／17／25／27／74的令牌不进入该池；每次借还均执行十二个个别 TOK 和阶段 CTL，
部分转交时没有 helper 运行。RG invocation 与 dispatcher 的 source token 各自独立。

在这一个 boot 实际执行四份 AA20.1 分配／授权初始化，取得互异 alpha 根
$O,F,N^*,r_0$。各 parent／left／right／header 置 null；各真实 allocator-returned 引用
只写入自己的固定根槽一次。四份驱动器各有真实当前 grants、request／reply／End／local ACK／same-root Return
连接束。$O,F,N^*$ 供 mode10；$r_0$ 是 mode01 的唯一 arena driver 根。
新 cone 不是独立 source，也不取得新 driver、根槽或每轮授权。

在 $O$ 完整执行旧 (AS.1)
$P_\varepsilon,S_\varepsilon,S_L,P_R,S_{LL},P_{LR},S_R$，
每项含全回复、祖先 Maintain、End、局部 ACK、同根 Return及清理，写出／检查完整 boot-done backing。
$F,N^*,r_0$ 此时保持 alpha。即使某分支不用这些材料，四根和全部 boot 事件仍真实存在并计费。

**定义 27.2（有限 supervisor 与连接）。** 一个有限 supervisor 有 backend=legacy／arena，
四个固定 driver case，初始化／请求／结算／停车阶段；真实字段保留 reserve 路径和引用、
selected descriptor、binding tail、active call、candidate descriptor、source／token cache、
解析栈、输出缓冲和 pending I/O。路径、ordinal、引用、栈和历史长度是分配记录中的有限数据，
不成为随未来轮数增加的控制标签。

保留五条外层有向连接：P request→supervisor、supervisor reply→P、P PayloadACK→supervisor、
A settlement→supervisor、supervisor settlementACK→A。Init／InitACK 分别复用前两方向的互斥阶段，
Park／ParkACK 分别复用后两方向的互斥阶段。各 endpoint、空／满、latch、backing、子阶段均实际构造。
原48／49／50／51路线与这些连接分开，确认各有自己的方向、语法和使能边。

**定义 27.3（表、类型与描述的先后）。** 先对完整 RG／CAP／旧 AS 图和本增补各固定过程作
hygienic 有限联合，包含两种字库 parity、固定端口／operation／fault／return cases，
Init／InitACK／Park／ParkACK，FAM-INPUT、FAM-T、FAM-RHO0、FAM-F7-HOLDER、FAM-F7-ASSOC，
八引用组件、28字段、Companion／Q／sidecar／Wait／M／ACK／Done／receipt、parse-frame／top／result及 pack 类型。
按定义1.4的长度分离字 $1^{m_0+1}0U(j)$ 在旧有限表后连续编号；固定调用点内联，返回边字面化。
所有变量深度解析使用第32节的数据栈，不递归安装控制代码。

按定义14.2的首次文字出现序得到有限 resident 表 $R_N,R_A$ 及 registry $\mathcal R$。
表外真实安装先写表，后写

$$
\mathscr D=T_4(\mathtt{J\text{-}FAMILY\text{-}ARENA\text{-}1},
\operatorname{enc}(R_N),\operatorname{enc}(R_A),\mathcal R),\qquad
I=T_4(\mathtt{RBG1},d_P,d_P,\mathtt{1100100000010}).
$$

$\mathscr D$ 的 P21 payload、P17 十域描述符、status 完成后才有真实 $d_P$，再写 $I$ 并取得 $i_P$。
实际 CAP 全复制在 A 形成不同 local references，origins 分别为 $d_P,i_P$。
所有新行使用这个安装的真实身份，resident 行没有自身描述、未来引用或未来 root 值的字面常量。

**引理 27.4（有限安装与身份良基性）。** 定义27.1–27.3在假设26.2下给出固定有限 boot，
不依赖未来输入、未来完成轮数或停止 horizon。

证明。联合的过程、端口、类型、固定字段及返回 cases 有限；循环只消费实际字／链。
先有表，再有表外写出的描述及引用，再有身份及引用，后来的 parent 对象只指向已完成对象。
根槽只含真实分配绑定，变量路径不被转换成引用。四份 AA 初始化和旧 $O$ 七事件有各自完整生命周期。
因此没有自描述环、每轮新 grant 或无授权入口；额外三 legacy 根只是明确的有限安装成本。$\square$

## 28. 原 Lift 与 arena 初选的实际接合

**定义 28.1（Native 的共同起点）。** 执行本 boot 唯一 CAP／RG beta ingress／validation、
源布局、counter／directory、boot／prior、stationary seed acquisition及完整种子返回。
按 RG2.2 在第一次 RG append 前保存实际原 table24、完整 configuration25、空 waiting27和头距离，
连同初始化／seed／code bindings存入互异持久字段。实际 mode bits 决定原分支；
mode01／10才将原 invocation 一次 TOK 到 RG 槽。

mode01 保留四次原 Lift：Reserve3、Raise3、Rho、Rho；每次完成原响应、行／依赖、ACK、
source-token／idle和返回状态安装。得到特定 sealed CompletedLift，source 为 $E(\beta)$，
$h=K=3$，pool 在其完整返回后的 A 阶段。这里没有把 AA 初始 alpha 说成原 beta。

**定义 28.2（Init 的实际取得与第一 cone）。** 在普通首次 Entry 前，A 在新 Close29 界内
重载该 CompletedLift及真实 seed／boot／prior／source bindings，由已取得 beta seed 用原替换／遍历字程序写

$$
S_{init}=T_4(\text{lift-state-origin},\text{complete-lift-state},
\text{actual-derived-beta-word},\operatorname{tok}(E(\beta))),
$$

再测量导出／封存

$$
Init=T_7(\mathtt{FAM\text{-}INIT},I,SourceBindings4,
\text{full-acquired-seed-and-binding},\text{full-CompletedLift},S_{init},\text{actual-lift-final-origin}).
$$

全部子域先完成。Init 经完整49到 P21／17，完成 receiver checks／ACK／全池归还，
然后十二 TOK 到固定 InitForward。dispatcher 仍持 idle source token，没有 source admission。
P 完整读其本地已收块，发送 $0010\,B(Init)\,010$。
AA 在逐位 backing 后全查版本／身份／$\xi$／seed-beta／lift-state／witness／ending。
嵌入的 foreign occurrence words 是谱系键，只对声明且已取得的本地 payload 解引用。
真实性由真正 Native writer／copy 归纳承担，不由 AA meter 或一个状态数值承担。

在 $r_0$ 完整调用 $P_\varepsilon$、Return，再 $S_\varepsilon$、Return。
由 owner 在 stationary Ready 读真实 right field 得到 alpha-born $r_1$，保留
$(r_0,R,r_1,\text{actual-creation-Growth})$；读 left field取得继续 beta reserve，路径 $q=L$。
以第29节 Build 消费实收 $\operatorname{tok}(E(\beta))$，在该 alpha-born cone 实际构造 $E(\beta)$。
再用全新实际 Tag 遍历比较全字，封存初始 $B_0$，保留真实 descriptor及完整 Init acquisition。

**定义 28.3（InitACK、carrier及首次 Entry）。** AA 封存／打印
$0110\,B(Init)\,010$，进入 AwaitArenaRequest。
P 完整 backing／检查 InitACK的首尾及全 echo，在76归档；按完整48将真正收到的整帧复制到 A28／29，
所有分配、检查、ACK、pool 借还完成。P 规范角色／Tail13、17，再借池到 InitReturned。
A 新 Close29，用该 echo 的特定 origin检查自己的 Init和特定 CompletedLift，写初始 carrier

$$
T_5(\mathtt{FAM\text{-}INIT\text{-}RECEIPT},\xi,\text{lift-final-origin},
\text{actual-Init-A-reference},\text{actual-InitACK-A-reference}).
$$

重载同一个 CompletedLift，按原 continuation 所需测量导出／封存完成 Lift 状态，
十二反向 TOK、恒等角色 CTL、Tail13／17及原 Entry 边真实执行。RG invocation 始终未离开原槽。
$N=0$ 直接使用此 Entry及初始 carrier，随后真实 finish；不伪造 selected-final packet或 $Y$。

**引理 28.4（实际初始关系）。** 在假设26.2下，定义28.1–28.3有限达到上述首次 Entry，
Native source和所选真实 cone body均为 $E(\beta)$，但保留各自不同身份及历史。

证明。RG2.2、6.3、7.1给出实际保存 client和四次完整 Lift；Reserve／Raise保持 beta，
两次 Rho 的候选依次有2、3叶，真实接受。定义2.1–2.6及 CAP6.3供应测量写入和完整 owned copies。
AA20.3供应每次 P／S／Tag 完整返回，AA17.2经出生类型检查供应首 cone 的 Build。
实收 Init先于 $B_0$，其全 echo先于 A carrier，carrier先于原 Entry；辅助工作不改 Native 源、布局或计数。
这些是同一实际相继出口，非分别选出的兼容 endpoint。$\square$

## 29. 共享 spine、出生类型构造与真实候选取得

**定义 29.1（fresh cone 的取得）。** 保存实际 beta reserve 引用及其 backed 路径 $q$。
每次 $j>1$ 从 $r_0$ 固定 driver发送普通 $S_q$，完整取得并检查 Growth(S,q)、End，
封存 backing、local ACK、same-$r_0$ Return／cleanup／Ready。
此时 owner 从 reserve 的真实 right field取得新 alpha-born $r_j$，从 left field取得继续 beta，
写 $p_j=qR$、$q:=qL$。descriptor 是真实 auxiliary record，含 $r_0,p_j,r_j,parent$、
实际 creation request／Growth backing及后来观察／history cuts；最后才 seal。
从初 cone起 $p_j=L^{j-1}R$。ordinal或路径从不被 cast 成对象引用。

各 $p_j$ 前缀不可比。未来 reserve splits和其他 cone edits不写旧 cone 的 source interior或内部 tapes；
但确实改变共享 scaffold 祖先的 routing tapes。每次原 Maintain从实际 target沿真实 parent走到 $r_0$，
逐祖先比对 child fields并追加实际 L／R；非 null cone parent和全部这些变化始终保留。
因此这是一个源的实际子树族，与 legacy 三个独立根不同。

**定义 29.2（Do、ReadBody及出生构造）。** `Do(kind,a)` 在当前 cone上构造完整 AA20.2 请求，
全局地址为 $p_j a$。请求 Tag／P／S／HasPromotion／HasSplit／FetchGrowth／Next仍为000至110，
地址为 $U(|p_j a|)(p_j a)$，L0／R1，Growth的 kind P0／S1。
完整发送、实收 tagged reply／End、seal副本、local ACK、same-root Return／cleanup／Ready后才执行后继。
Growth须匹配实际 kind／地址，保留请求／reply／creation／maintenance关联。
驱动器每次正常 Navigate／Guard重新到达目标；supervisor不传 raw-reference operand绕过根。
owner额外字段读取只在自己的 driver已返回、stationary且权限有效时执行。

ReadBody(p) 分配实际路径栈，初含 $p$。pop后真实 Tag：alpha追加01，beta追加10；
branch追加11并压 right后left；absent进入 fault。所有栈／输出节点先写 bit／path／next，再链接；
空栈后才封存完整 acquired word。遍历期间源静止，物质 unary marker不入栈。
Tag本身不返回引用；需要的真实引用由 owner的已授权字段路径另取得并与普通 navigation相符。

Build(span,p,birth) 是 AA17.2 的实际出生构造。帧含已取得 immutable input ref、offset／length、
backed global target path、birth alpha／beta和 next。先以 open-slot完整扫描验证恰一棵 token tree、
准确耗尽；短字、多树、PAD均失败。target alpha要求 birth alpha且不编辑；target beta仅在 birth alpha时 P；
target branch仅在 birth alpha时先 P，随后 S。branch后实际完整前序扫描确定左右子 span，
压 $(right,pR,alpha)$ 再压 $(left,pL,beta)$。每次编辑均为完整 Do。
位访问、Add／bounds／split-point／push均由真实列表和字段操作执行，未增加 Clone、graft、reroot或Serialize原语。

**引理 29.3（所需出生类型）。** 所用目标 $E(t),E(v)$、其 ordered pairing及随后 rho结果，
均处于 AA17 的可达域；在 beta-born graft child处也满足出生约束。

证明。$E(\alpha)=\langle\beta,\alpha\rangle$、
$E(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle$，且 $E$ 保持配对。
二者没有 L-ending alpha叶；结构组合保持该性质，根均非 alpha。
故在 beta-born root无需非法 P，也不会要求 beta变 alpha，内部出生条件逐点满足。
AA17.2给出每个实际事件前缀合法性。rho复用 LAB9.3–9.4在 $\mathcal D_+$ 的旧frontier结论。
这只是这些已有定理的参数核对，不另立可达性基础。$\square$

**定义 29.4（三种操作驱动的 candidate）。** 每次 selected final，先以 ReadBody(selected.path)
取得真实旧 body全字，并与新收到的 $S_w$ 全等；selected必须是 current sealed binding中同一个 owner-held descriptor。
graft 的 $T=\operatorname{tok}(E(v))$ 来自原 canonical prefix parser／converter，
其 mandatory P21 backing和 Q ContextOption均实际存在并另验证。私有 source16及树名不是 supplier输入。

Left：取得新 alpha cone，root完整 P再S，在 beta-born LEFT child Build实收 $T$，
在 alpha-born RIGHT child Build实际取得旧 body，得到 $\langle E(v),E(t)\rangle$。
Right：新 cone root P再S，在 beta-born LEFT child Build实际旧 body，在 alpha-born RIGHT child Build $T$，
得到 $\langle E(t),E(v)\rangle$。不输入 Native拼好的候选，也不把 LAB的计数 action G当作 Right。

Rho：取得新 alpha cone，先 Build实际旧 body；在任何后续编辑前实际 Tag遍历并封存其旧逻辑叶frontier。
每项保留实际 global address／已取得 alpha或beta tag，并由 owner正常字段路径取得目标引用。
仅按该旧链：alpha执行 P，beta执行 S；每项完整返回后前进；新生叶绝不加入旧链。
不同旧叶前缀不可比，另项编辑不移动其真实根引用；实际 Guard／祖先维护仍逐次执行。

candidate完成后必须再作一次新的 ReadBody(candidate.path)。只有此次真实 Tag位经编码转换形成候选值；
实际数 active tokens，补 PAD至收到的 operation-dependent $c_{\rm cap}$，不能容纳则 fault。
全位、长度和 Q关联完成才 seal outbox。Build输入、$S_w$、请求 echo均不替代这次候选取得。

**引理 29.5（literal candidate与完整内层返回）。** 假设26.2及上述真实入口下，三种算法有限完成，
新 cone恰为原 selected candidate $c_{\widehat A}(E(t))=E(c_A(t))$，outbox恰为其 padded Native token全字。
旧 selected cone interior不变；共同环境历史真实延长。

证明。出生类型引理和 AA17.2给出两次 Build各自逐前缀合法性；实际固定根 navigation及 AA20.3给每次完整返回。
Left／Right的两个真实 child位置直接保持顺序。Rho在 sealed旧叶链逐项使用原 P／S，
保留原 branch与次序，故 LAB9.4／定义16.4–引理16.5的结构论证给 literal rho，不只是叶数。
RG (RG.2)供应 encoded candidate等式。最后新 Tag traversal和逐位写入给 outbox；
共享 parent链上的每次 Maintain保留 AA19.1–19.2的全真实 routing tapes。$\square$

## 30. 每次实际调用的发生键与完整旧回执

**定义 30.1（原调用入口与 Companion20）。** 只在 mode01 selected computed final的
sealed ComputedWait之后、原 packet send之前插入适配。原 raw staging／raw return、独立 GuardIngress、
$G_i$、Plan、Reserve／Raise及其返回均保留。A完整重载本次状态，用定义15.1的实际字程序写
$S_w=T_4(wait\text{-}origin,\text{完整wait},t,\operatorname{tok}(E(t)))$；
$t$来自真实 seed及先前已安装完整回应，不读取 Native私有源。

Companion20前17域依次是：版本、实际 packet27-ref、完整 packet、实际 waiting25-ref、完整 waiting；
完整 $G_i$、guard-ref、完整参考守卫、proposal-origin、完整 proposal；
$\xi$、实际轮 $U(i)$、previous-semantic-end、previous-unified-end；原 $k,z,c$。
后三域为 RG01、完整 $S_w$、本节精确定义的 previous-receipt option。
A先完整 route49发送 Companion、完成 check／ACK／全池返回，再完整发送原
$T_4(\mathtt{RG\text{-}CALL2},k,z,AfterFinal)$，最后十二 TOK到 P。
P全查两份实收 local blocks的 origins／mode／source／round／guard／proposal／wait／predecessors及 $k,z,c$，
再由原 CAP自动构造真实 header／length／payload三块，canonical count仍为3，没有新的 final-frame IN。

**定义 30.2（实际回执 bundle及本地化）。** $i=1$ 使用定义28.3的真实初始 carrier，
连同实际 Init／InitACK／lift-final bindings，编码
$0\Vert T_4(\text{complete-initial-carrier-payload},\text{complete-Init},
\text{complete-InitACK},\text{full-root-key-table})$。
root-key table标识这些实际 acquired对象；其中的引用字不授 AA driver权限。

$i>1$ 时 A新 Close29，在固定已完成前缀全扫 FAM-RECEIPT，按 $\xi$、completed round $i-1$、
$G_i$所记确切 preceding-selected-final origin筛选，要求恰一匹配；不是 LatestType。
完整检查 descriptor／status并取得它所指的全部早先 M、Done及实收 ACK的 length／body／ending。
ACK全字由实际已经完成且 status通过的这三块组装，不重新生成同值字冒充收件。
previous-receipt的 present语法为

$$
1\Vert T_4(\text{ENTIRE actual prior M},\text{ENTIRE actual prior ACK},
ReceiptCatalogue,ReceiptRootKeys).
$$

ReceiptCatalogue 为 $U(d)$ 后恰 $d$ 个五 $B$ 域项
$(role,\text{full-original-origin-or-local-key},\text{actual-A-local-ref},type,\text{complete-payload})$，
最后耗尽。ReceiptRootKeys标识 actual carrier、Done、Wait、captured-response-state、
original-waiting-packet、M、ACK-parts。

A用实际 pending／completed完整键列表，在该新 Close29前缀上计算这些 roots的全 typed backward closure。
逐个真实 descriptor／seal／status／origin／owned-port读取，并用 protected-head import恢复输入头。
包括 reader真正跟随的每个 Wait／Done／captured-state／packet／M／ACK／carrier及其所需旧 public dependencies；
source handles／keys／payload均早于本 Companion。未被声明为解引用的 state内部发生字仍仅是谱系数据。
A保有自己的25／27／28／74 tokens；不存在 P或AA对 A这些端口的暗中读取。

整个 bundle作为真正 Companion字节经49进入 P-local immutable Companion，再作为 Q的一部分实际传给 AA并逐位 backing。
P／AA reader把其中 A-reference words解释成 LINEAGE KEYS：全解析 catalogue，完整键匹配、type及耗尽检查后，
得到该已收容器中的实际 payload subspan。subspan由真实 input ref、offset／length、Add／At及有界位扫描定位，
不是伪造的 CAP child reference，也不授远程权限。重复全键必须有相同不可变实收 payload，否则 fault。
只有 Input22其他明列 P-local CAP references走 P17／port／status路径。
AA另把全 prior M／ACK、occurrence／binding与自己 retained binding tail、真实 prior received M、prior printed ACK逐位比较。
更新的 raw或maintenance unified ends不替换 preceding-selected-final origin。

**定义 30.3（Kcall、真正 referent及 association）。** 每个选中 final的两个实收 P-local allocations和原 A packet发生，
在 F7前形成并由 Raw21 backing

$$
K_{call}=T_5(\text{actual-P-call-local-ref},\text{actual-P-companion-local-ref},
\text{original-A-packet-origin},\text{actual-round},\text{actual-guard-origin}).
$$

只在真正 source admission后、唯一 source-start fence前执行一次本调用 F7Stage。
graft完整原 prefix parser／converter得到 $d,M,T=\operatorname{tok}(E(v))$，Raw21以 FAM-T写全 $T$。
Rho联合检查001、空 $z$、canonical零payload及三个 absent options；
真正 New／Append0／Finish构造一位0，Raw21以 FAM-RHO0写入。Rho的空 $z$另有真实零长度块，与此 marker不同。
两个 Raw真实返回八域 referent

$$
r_7=T_8(U(P),U(17),U(c_7),U(21),U(b_7),U(\ell_7),\tau_7,U(b_7+\ell_7+1)).
$$

$\ell_7=2M$、$\tau_7=$FAM-T，或 $\ell_7=1$、$\tau_7=$FAM-RHO0。
十域实际 descriptor为 $(P,21,b_7,\ell_7,c_7,\tau_7,1,0,b_7+\ell_7+1,\epsilon)$，
数字按各自原 unary编码。Base／干长度／FieldBody／sep／status0／不同输出 Add／真实 ordinal／十域／seal／
At-WR1-CTL／八域引用／恢复角色，全部采用定义2.1，目标关闭前无嵌套 Raw。

F7返回后 Raw77以 FAM-F7-HOLDER把整个 $r_7$作为 payload写入，取得不同的 holder reference $r_H$；
再 Raw77写
$Assoc=T_4(K_{call},r_H,r_7,\mathrm{operation})$，类型 FAM-F7-ASSOC。
freeze此时完整 P17 count，在任何 lookup输出前全扫恰该 prefix中所有完成 associations，
每项 payload／descriptor／status全部读完，按完整 Kcall及 operation筛选，要求恰一匹配。
保留其真实 ordinal／payload；完整读取实际 holder，要求整个 payload等于该 $r_7$；Input22.7必须同一 $r_7$。
ordinal是扫描键，非头位置；$r_H$、同类旧 referent、同值旧块均不能代替它。

**引理 30.4（任意轮的 occurrence binding）。** 在顺序合法调用中，上述 association存在且唯一，
回执所需每一字节均来自已实际取得的本地容器；重复同值请求不改变其所选发生。

证明。每个 fresh packet／Companion有自己的完成 allocation／copy occurrence，实际 round／guard／proposal bindings
在本次 F7前完成；不同 selected finals的完整 Kcall不同。单 admitted调用在固定阶段只写一个 association，
其 $r_H,r_7$来自本次刚完成的两个 Raw；frozen-prefix全扫排除所有旧键并命中此项。
完整持久块不被下次同 type覆盖，八域／十域／status读数把该项接回真实 writer。
previous receipt从前一真实 final occurrence定位，其所有 followed bytes在 Companion／Q中实际复制，
全键局部 subspan读取不会制造 remote read。AA retained M／ACK／binding提供另一个实际比较端。
因此不以一个假定 dictionary、数值 origin或同值新回复补齐重复调用 seam。$\square$

**定义 30.5（完整 Q24及唯一 fence）。** 实际取得旧 $h,K,r,p,v,q,g_c,e,j,m$和两 ends，
将旧十字及互异 $q^+,g_c^+,e^+,j^+,m^+$分别完成保存。F7／holder／Assoc完成后，
写完整 before-manifest，只执行一次真正 source-start CloseFence，保存其真实六域及引用。
Attempt6恰为 call-origin、companion-origin、round、guard-ref、$c$、start-fence-ref。
Q24依定义15.4的24域顺序：

| 域 | 本调用真实完整内容 |
| --- | --- |
| 1–4 | family Q版本；Attempt6；companion-origin；完整 Companion20 |
| 5–7 | call-origin；原 canonical count3及三完整引用；原实际 $z$ |
| 8–10 | ContextOption；dOption；MOption |
| 11–15 | 实际旧 $U(h),U(K),U(r),U(p),U(v)$ |
| 16–18 | $U(N_s),U(c_{\rm cap}),U(L)$ |
| 19–20 | 实际 start-fence完整六域；实际 $d_P$ |
| 21–24 | 原 operation；RG01；完整 $S_w$；完整 previous-receipt option |

graft的三个 option依次恰为 $1\Vert T,1\Vert U(d),1\Vert U(M)$，$d\ge1,M=2d-1$；
Rho各恰一位0，不存在 $d,M,T$，不用 $M=0$。在真实 post-maintenance $h$重算

$$
N_s=2h-1,\qquad c_{\rm cap}=\begin{cases}1+N_s+M,&Left/Right,\\3N_s,&Rho,\end{cases}
\qquad L=2c_{\rm cap},\qquad W=3N_s+c_{\rm cap}+8.
$$

参考守卫 $g_i$不是此处 $h$。Q没有 $r_7,r_H,Input22$引用，也无新增 canonical operand block。
所有嵌套字段／快照先完成，才写 Q父字；到第一 source STORE前辅助工作保持源、目录和旧 counters，
$f$只随实际 fence增加，不恢复旧 $f$。

## 31. 五帧、真实 IN／WR bank与全部28域

**定义 31.1（完整外层运输）。** 逐字保留定义19.1的五帧：

$$
\begin{aligned}
Request&=0001\,B(Q)\,010,\\
RequestACK&=1001\,B(Q)\,010,\\
Response&=1100\,B(Q)\,U(c_{\rm cap})U(L)\,outbox[L]\,010,\\
PayloadACK&=1010\,B(Q)\,U(L)\,010,\\
Confirmation&=1011\,B(Q)\,U(L)\,010.
\end{aligned}
$$

$U(k)=1^k0,B(x)=U(|x|)x,T_r$为恰 $r$个 $B$域串接；物理 sep／status不混入 wire。
P76逐位保存完整实收 metadata／echo；AA发送前亦有封存 backing。
Response metadata完成检查后才测实际 Base16，reserve恰 $L$位、sep、status0及实际 unavailable十域 bank descriptor。
每个真正 AA OUT位由 P IN后直接 WR该 bank，backing完成前 latch不释放、下一 OUT不使能。
完整 payload／ending／descriptor／status检查后才 status1并取得 $r_B$。
完整 PayloadACK被 AA接收／检查后才 delivered，再由真实 ACK构造 Confirmation；P完整取得后才 DA6及 Input22。

位前缀归纳给出：第 $t\le L$位后，bank前 $t$位与这个 sealed outbox前 $t$位相同，
游标／计数和 pending latch也对应；$t<L$时仍不可用。
所以这是定义5.2的 B6star真实 exclusive IN-WR关系；Q／DA／flags／等长 echo本身不能认证 payload。

**定义 31.2（完整 Input22）。** 在五帧、available bank、DA完成后，
按定义2.2先准备每个子元组／独立字段快照，再 Raw22写下列恰28域。
第1域 ASCII tag及其 descriptor type均是本 family新版本，不能以旧版本作另一入口。

| 域 | 完整实际内容 |
| --- | --- |
| 1 | FAM-INPUT的固定 ASCII-bit tag |
| 2 | available immutable bank完整引用 $r_B$ |
| 3 | 实际 acquired P-local original-call reference |
| 4 | 实际 acquired P-local Companion20 reference |
| 5 | 原 canonical count3及三个完整真实 references |
| 6 | 原实际 $z$ staging reference；Rho亦有独立真实零长度块 |
| 7 | 定义30.3同一 occurrence-associated referent $r_7$，不是 $r_H$或 option |
| 8 | $T_6(dOption,MOption,U(N_s),U(c_{\rm cap}),U(L),U(W))$ |
| 9 | 实际旧 $h,K,r,p,v$ staging references五元组 |
| 10 | $T_2$（旧 $q,g_c,e,j,m$五引用，五个互异实际 prepared-plus-one引用） |
| 11 | $T_2$（old semantic-end option，old unified-end option） |
| 12 | 实际取得的完整 $G_i$ staging reference |
| 13 | $T_2$（original guard reference，actual complete acquired-copy reference） |
| 14 | $T_2$（original proposal reference，actual complete acquired-copy reference） |
| 15 | $T_2$（original waiting reference，actual complete acquired-copy reference） |
| 16 | 完整实际 Attempt6 |
| 17 | 实际 Q24 reference |
| 18 | 实收完整 RequestACK reference |
| 19 | $T_2$（实收完整 Response metadata reference table，actual DA reference） |
| 20 | 实发完整 PayloadACK reference |
| 21 | 实收完整 Confirmation reference |
| 22 | 唯一实际 source-start fence reference |
| 23 | 完整 actual before-manifest reference |
| 24 | $T_4(\xi,boot,prior,seed)$完整 original bindings |
| 25 | $T_2(d_P,i_P)$实际身份／描述引用 |
| 26 | $T_5$（original caller-kind，AfterFinal，ComputedReturned，FAM-LEFT／FAM-RIGHT／FAM-RHO，ServiceReleased） |
| 27 | 恰九位111110000 |
| 28 | $T_5$（actual call-origin，guard-origin，proposal-origin，round，previous-selected-final-origin） |

第27域依次记录 bank-ready、echo-checked、response-complete、payloadACK-sent、confirmation-checked为1，
settlement、source-write、candidate-read、candidate-parser-read为0；不能用这些位代替独立检查。
第7域对父字贡献是 $B(r_7)$。先全字段 Raw77快照，再 New11、逐域 preserving Reload／Frame、
Finish11／Copy到1、Raw22、真实 descriptor／status1；目标开启时只有允许的字面追加／Frame／Reload，
不在同目标读源或嵌套 Raw，不以未来父 base／length作 backing。

## 32. 全 decoder、可变深度数据栈与实际后置 BIND

**定义 32.1（28／8／10完整扫描）。** 先归档实际 handle，检查其全八域 reference及实际十域
P／17／22 descriptor、ordinal／base／length／family type、seal、initialized1、mutable0、空 origin、
实际 status地址等式、At／RD status1、arena／range。
28个固定 pass均从 Input22实际 base重启全长预算，完整消费恰28个 ReadFrame，
检查 exhaustion和物理 sep；第 $j$域仅在该整遍关闭后保存。Rho的第7 frame同样每遍消费完整 $B(r_7)$。

在解释 referent前，完整解析实际 call、Companion20、Q、mode／round／wait／guard／proposal／receipt及第26域五字段，
共同确定 operation。type自身不决定 operation或可调用根。
随后八遍完整 reparse $r_7$，每遍八 frame／耗尽／sep，关闭后才保存一个组件。
完成定义30.3的完整 association frozen-prefix查找和 holder全 payload比较。
freeze完整 descriptor count $D_7$，十个固定 pass均全读所选 actual descriptor的 tag／十域／seal，
关闭后才保存一域，逐项比较

$$
(P,21,b_7,\ell_7,c_7,expectedType,1,0,b_7+\ell_7+1,\epsilon).
$$

状态地址用真实 unary Add及不同输出构造，实际 At／RD status1及 P21 range通过。
未来快照用其后来另闭的界，不在 $D_7$寻找尚未完成对象。
graft完整复制 $2M$位、sep／status，重做原 $z$ conversion／tree grammar及 $d\ge1,M=2d-1$，
与 Q和Input22三 present options全字接合。Rho只读 typed一位0及sep／status，
查 canonical001／空 $z$／真实零长块／三 absent options／FAM-RHO；
其内部结果只是 NoContext-validated，不产生 context vector、$d,M$、空树或 context reference。

**定义 32.2（其余全部 nested checks）。** 下列 reader逐字段全预算扫描、全结束检查后才保存，
ReadUnary／ReadFrame实际逐位消耗预算；空域是空字，缺0、越界、多位均失败。

| 对象 | 完整语法及关系 |
| --- | --- |
| canonical request | unary count恰3，三个全 reference frame并耗尽；header三位、全 unary length及完整 payload各有真实 sep／status／origin；全比对原 $k,z$ |
| Companion／Q／$S_w$ | 恰20／24／4域且耗尽；wait按 RG3.1原语法全读，seed／boot／prior／source／mode／stage／round／counts／两ends／真实回应谱系相符，重算 $E(t)$；三个 options各自耗尽 |
| previous receipt | 完整 initial或present语法、count及五域 catalogue；全 M／ACK、RootKeys、Done／Wait／carrier／captured state／packet通过实际 received-container subspans取得；AA另比 retained binding／attempt |
| old／prepared | 第9域五引用，第10域两组各五引用；读真实十旧字，Add1重查五个互异prepared字并比ReadState／Q |
| ends／$G_i$／guard／proposal／waiting | 第11域两个option；$G_i$含版本、$\xi,i,s_-$、preceding-final、guard-ref、proposal-origin、完整守卫；第13–15域各两项完整 original／copy绑定；守卫单调、proposal／ComputedWait和两个各自前驱全查 |
| Attempt／fences／manifest | Attempt恰6域；fence恰6域，kind／$f$／tick／fee／$\xi$／directory和实际引用相符；manifest按实际count及tag00／01／10的6／7／5域全读、耗尽，比真实before-state |
| transport／DA | RequestACK全头／length／Q echo／ending；Response六块、Confirmation五块及完整 $U(L)$；DA6的Q、Response、实发ACK、Confirmation及flags均与真实attempt／origins相符 |
| identity／return | 第24域4绑定、第25域2引用；真实 $I$恰4域且两个description refs均为 $d_P$；第26域恰5和固定case、第27恰9位、第28恰5发生绑定 |
| dimensions／bank | 第8域恰6，重算 $N_s,c_{\rm cap},L,W$；bank descriptor为 $(P,16,b,L,c_R,T_{bank},1,0,b+L+1,\epsilon)$，全引用／seal／status1／range／非别名；不 RD candidate bit |

foreign origin只解析到声明且已取得的 local copy或容器subspan，不反向追 remote物；
物理 Native descriptor的 $D(w)=w\mathsf{sep}$与 wire的 $B(w)$分开解析。

**定义 32.3（可变深度 immutable parser stack）。** 旧receipt／catalogue可以任意有限深，
不能靠增加有限 outer arities或一句“递归 decoder”完成。
P在77实际写 immutable FAM-PARSE-FRAME：grammar-case、实际 immutable input reference、
backed offset／remaining-length、next finite field／list phase、较早 parent-frame reference、expected occurrence、result slot。
Top／version记录按完整 active Kcall和 parser invocation／pass键控；在恰该key的完整 bounded扫描中选择最后 completed version。
不按全局最新 type选另一次调用的 frame。

push child前先完成／snapshot当前 reader；child是同一个较早已收 immutable input的已验证严格较短span，
或 frozen INPUT bound内的声明 typed reference target。return时验证 parent／case／slot，
再追加parent的新 immutable version。子span预算0且其规定framing边界成立才完成；
实际physical块的末尾另检查真实sep／status，不在inline B域之间虚构sep。
固定case表恰为本节及定义18.4、20.3的 tuple／list／reference／manifest／row／M／ACK／receipt语法；
input bitstrings不能选择新代码。full-key pending／completed lists遍历有限 typed closure，新 target仅一次。
origin不反向跟随，typed依赖指向较早完成对象；inline子frame严格缩短span。

明确保留两个不同界限：实际 INPUT对象的 frozen descriptor／catalogue bound，及当前 parser已封存 STACK／TOP的
后来新 closed bound。新 frame／top／snapshot输出不加入 INPUT closure，不能令读取者追逐自己写出的尾部。
Raw77 frame write和 Raw21 selected-field save只在当前 scan关闭后执行。
每个 Raw返回的 frame／top reference在任何 helper覆写工作角色前亦先真实 backing。
局部 subspan由真实 unary Add／At／bounded scan定位；没有随机访问字典或凭 numeral制造 CAP引用。
AA的对应 parser以实际 auxiliary frame／top／marks／cursor／result records逐字段实现同一固定case表，
request backing和closed catalogue是其本地 immutable输入，stack是另外的实际物质。

**引理 32.4（全历史读取有限且保持十二字）。** 在本构造已取得的有限输入上，定义32.1–32.3
完整读取所有保留字段，有限完成，原十二工作字及 backing纪律不被可变历史深度破坏。

证明。28／8／10固定pass各在关闭源扫描后写输出；定义2.2以1–10运行 Reload，11保护活动prefix、12保护预算。
一个 frame所需跨helper活值都已经封存；Raw内部不再嵌套Raw，后续lookup取真实较早frame。
inline descent消耗较短有限span；reference discovery只增加 frozen finite INPUT集合内未完成的全键，
较早依赖无未来环，completed阻止重复访问。每个frame的有限字段／剩余列表阶段消耗实际预算，return有封存parent。
STACK新记录只能被自己的另闭界读取，不扩大INPUT；所以没有自追尾部的非终止。
full catalogue scans和实际 local subspan检查使每个receipt字段都有已收位，不以opaque外来handle补洞。$\square$

**引理 32.5（真正后置 BIND）。** 上述全 decoder成功后，恢复实际 ReceivedBankEntry角色／头，
此时才测现在的 Base22，保存 rb22-start，按定义6.1真实 append／seal
$BIND(r_B,\text{actual-call-local-ref},\text{actual-Input22-ref})$，arity仍为3，进入 BuildForest。

证明。定义2.1–2.3供应每个实际writer，定义30.4固定本调用 referent身份，定义31.1供应bank位。
各全pass／typed输入／stack归纳供应实际消费字段。所有 Input22／sep／status和decoder快照均已完成，
因此新的 Base22位于它们之后；Append22写出的BIND引用同一真实handle，不是假定关系或额外原语。$\square$

## 33. 只替换选中 candidate依赖的完整原程序

**定义 33.1（删除片与所有保留工作）。** 仅对本 selected final，将每个 candidate-bit root换成 BANK。
一个前置只在它的所有活消费者都在该删除片内时才删除。
Rho删除 PR57.09的 chunk-length／private-offset／equality scatter及专属 folds；
Left删除 slot-zero／context／source equality scatter，Right删除 last-active／context equality scatter及其专属 folds；
相关专属 OR／PAD-fill输入一并删除。没有旧 scatter的 fallback，也不另跑一份 Native materializer验证 import。

原 raw staging保留完整原 materializer，含 raw Rho。完整原 canonical／prefix／context processing、
mandatory T backing、所有活 SOURCE消费者、$A_s,L_s,A_{N_s}=0$、unused常量／地址、
完整 signed-width parser、全部 arithmetic／MUX arms／final carries、所有 $2N_s$ result MUX roots和
随后所有 $2N_s$ ordered Resolve STORE、原 interpreter／cache／seek／BF／WR／recovery／terminal RD／exit，
均保留。清理仍全扫描规定 mutable scratch，排除 immutable bank／T／marker／holder／metadata；
response仍由真实 private $\gamma$投影写入、release及唯一 response-commit fence完成。
旧 archive、resident其他服务、旧program和所有 STORE效果不删除。

**定义 33.2（真实 forest及逐门发射）。** 从实际 rb22-start使用定义6.1、19.2的原生语法：
每记录 $D(tag)D(w_1)\cdots D(w_a)seal$，固定tag为110101加其原suffix。

| 种类／元数 | 原字段 |
| --- | --- |
| E6 | K、f、三个child unary、value |
| Q3 | EXPR／STORE、node、destination或0 |
| F7 | node、parent、slot、next、三个result references |
| R2；TOP1；CUR1 | node／完整result reference；frame或0；已完成Q数 |
| BIND3；FEND2 | bank／call／Input22；实际Q数／冻结forest记录数 |
| VBIT3；VEND2；BUILD6 | vector／index／root；vector／width；phase／slot／need-vector／leaf-vector／closed-root／valid-root |

Append22先全扫描／计数当前完整记录、准备全部字段快照后才打开目标；Lookup一次只保存一域，
跳过其他域并检查该seal，多域必须重复全扫描。Q只枚举 FEND冻结集合；后来 F／R输出不增加Q。
E的 K／f／arity严格采用定义6.3：CONST0／1、COPY／NOT／XOR／AND／OR／MUX、BANK、SOURCE、REF。
孩子须为较早sealed E；REF须命中较早 EXPR root；unused孩子为真正 $U(0)$，value按原语法；
错误K、错误8位truth table、非正或不更早孩子均fault。

按顺序构造全部 $2c_{\rm cap}$ BANK leaves及VBIT，全部 $2N_s$ SOURCE leaves和原 masks，
完整 parser／arithmetic／guard，再全部 $2N_s$ result MUX roots，最后才依 $i=0,\ldots,2N_s-1$写全部 STORE Q。
各向量有完整 VEND，BUILD保存整槽旧值，FEND在全部构造完成后冻结真实计数。
Rho的 NoContext不生成 context vector或field7 expression leaf；graft原T与完整检查仍在。

生成器复用定义6.4、19.4的 Active／Waiting／Push／ChildReturn／RootReturn。
Push先seal Waiting，再分配以该真实ordinal为parent的child；return全查node／parent／slot／next和空slot，
追加只填本slot的新parent版本。跨helper活值各有实际77 backing。Complete分配真实 mutable available一位W结果，
再Emit及R；REF只查早先结果，不递归展开旧证明。

真实分配并seal不可变一位0 dummy。BANK.value是 $T_3(U(c_R),U(s),b)$；每次全查BIND bank／descriptor／status，
用真实 unary Add得到 $2s+b<L$和 $b_B+2s+b$，不 RD candidate bit。
每个 SOURCE operand或destination均实际 Resolve到当前 $\phi_K$；其他W地址来自真实分配。
所有gate完整写为 $1f_0\cdots f_7U(d)U(a)U(b)U(c)$，
常量／一元门的unused地址亦完整存在并指真实dummy。
实际 Base15在本次生成前测，terminal0后测长、sep／status／descriptor／seal完成，
At真实base才进入不变 PR57.D4解释器。

**定义 33.3（原完整 parser／arithmetic）。** 初值 $(n,z,\ell,v)=(1,0,0,1)$，
每个候选槽恰计算全部

$$
\begin{aligned}
P&=[token=PAIR],&A&=[token=alpha],&B_\beta&=[token=beta],\\
\Lambda&=A\lor B_\beta,&T_c&=P\lor\Lambda,\\
I_{bad}&=([token=PAD]\land\neg z)\lor(T_c\land z),\\
n_*&=n+[P]-[\Lambda],&n'&=MUX(T_c\land\neg z,n_*,n),\\
\ell'&=\ell+[\Lambda\land\neg z],&z'&=z\lor[n'=0],&v'&=v\land\neg I_{bad}.
\end{aligned}
$$

全 $c_{\rm cap}$槽完成才算
$\gamma=v\land z\land[n=0]\land[1\le\ell]\land[\ell\le h]$。
PAD-before-closure和nonPAD-after-closure均无效；没有私有 early stop。
PR57.07的加法每位完整五门
$t=x\oplus y,s=t\oplus c,u=x\land y,v_*=c\land t,c'=u\lor v_*$，含final carry；
减法逐位NOT第二数、carry1进入同一加法；equality逐位NOT-XOR再AND。
PR57.08的 unsigned compare以old $e,l$完整算
$z_e=\neg(x\oplus y),n_x=\neg x,u=e\land n_x,v_x=u\land y,l'=l\lor v_x,e'=e\land z_e$，
共七门／位；signed先翻符号位。初始常量、复制和MUX三孩子全部生成并执行，未选臂不省。
公有整数位来自实际 unary倍增／Compare／Sub及VBIT重排，不预置私有计数向量。
$W=3N_s+c_{\rm cap}+8$保持定义6.6的范围：未选 $n_*\in[-1,c_{\rm cap}+1]$，
$\ell\le c_{\rm cap}$，$2^{W-1}>2c_{\rm cap}+2$，负一用同宽二补数，carry有真实位。

**引理 33.4（原效果、raw STORE cuts和真正释放）。** 在假设26.2及第29–32节真实入口下，
完整程序实际计算 whole-candidate guard，接受写整树，执行拒绝保留旧源但仍执行全部 STORE。

证明。candidate全字由新 Tag→outbox→真实OUT／IN-WR→bank→BANK projection传入，
引理32.5给真正BIND。定义6.6的parametric forest／frame／Emit归纳适用于实际正的 $N_s,c_{\rm cap},W$；
原PR57.L3、T1–T2的parser／MUX部分给 $\gamma$，不把已删scatter仍执行当作前提。
所有旧源位及MUX结果在首个STORE前已经算出。CAP4.3–4.5的稳定单射 $\phi_K$及fresh非别名分配保证：
执行前 $r$个STORE后，逻辑源前 $r$位恰为选中结果，后缀仍旧位；途中raw字不要求是合法树。
全 $2N_s$ STORE及高reserved位按原合同处理，$\xi$不变。
解释器仍逐条读完四地址、全部cache／seek／BF／WR／recovery，最后terminal-header RD／exit。
再真正分配unavailable response、以private $\gamma$投影、完整cleanup、status／release和唯一commit fence。
故 ServiceReleased只在这些实际尾部之后达到：P持全池和busy source token，真实 $Y$已保存，
旧／prepared counters和两真实fences仍在，此时尚未选择新event counters／rows；AA处于真正AwaitSettlement。$\square$

## 34. 全原记录、真正返回和可重复结算

**定义 34.1（真实Y之后的原计数与双链）。** ServiceReleased之后才读真实完整 $Y$，原 writer选择

$$
q'=q+1,\qquad g_c'=g_c+Y,\qquad e'=e+Y[operation=Rho],\qquad j'=j+1,\qquad m'=m+1.
$$

本 selected final保持实际 $h,K,r,p,v$；$f$包含真正两fence，不从old snapshot恢复。
raw和maintenance仍走各自原counter cases。严格按定义20.1先J15／index18，后U18／index19：

| 域 | 完整原语义字段 |
| --- | --- |
| J1–4 | SEG-J1；$\xi$；INITIAL-SOURCE的 $(tag,\xi,H_0,16,b_0,L_0,0)$；actual initial $H_0$/prior |
| J5–8 | postcommit $U(j+1)$；old semantic predecessor；真实operation；原canonical count3/material-reference word |
| J9–12 | 完整真实Y；before／after $(q,g_c,e)$六元组；历史 $U(h)$；完整SEG-SOURCE$(\xi,h,K,v,M_v)$ |
| J13–15 | actual I；真实start-fence-ref；真实commit-fence-ref |
| U1–4 | SEG-U1；$\xi$；actual initial $H_0$/prior；old $U(m)$ |
| U5–8 | old unified predecessor；同一operation；完整canonical refs；完整Y |
| U9–12 | before／after $h,K$四元组；layout／policy四元组；$q,g_c,e,j$八元组；directory count二元组 |
| U13–16 | 完整after-manifest；start-ref；commit-ref；no-publication option0 |
| U17–18 | option1加actual J mate；actual I |

append前完整 index18 count比OLD $j$，index19 count比OLD $m$；不能把 $j+1$当已有数。
maintenance后来新增的unified predecessor不替换semantic predecessor；两ends各自真实保留。
manifest及六域fence来自实际writer／读数，不在行内预写自身未来seal／fee。

actual J／U完成后才写 family15域sidecar，仍按定义20.2依次为
version、I、A original-packet-ref、P acquired-call-ref、A original-companion-ref、P acquired-companion-ref、
Q-ref、DA-ref、canonical word、c、old CountsEnds7、actual J-ref、actual U-ref、dP、Attempt6。
原48按boot／initialization／prior、canonical所有material、J、U的规定次序全复制，
再把新typed readers实际跟随的Q／DA／identity／sidecar／witness／receipt等PUBLIC依赖完整取得。
每个复制含sender descriptor、receiver allocation、mailbox、两全循环、status／seal、origin-to-local resolution、
copy-completion TOK及全部pool借还。P-local Input22／r7／holder／marker／bank／parser不虚增为public roots。

A在joined ends安装前完成所有row／dependency／identity／before-after／guard／layout／manifest／fence／
semantic mate／两个独立前驱／accepted-Rho e检查。全池回P后才原WHOLE-ROW ACK、source TOK回dispatcher、idle CTL。
此后ComputedReturned规范角色／Tail13、17、借全池、重载特定ComputedWait、新Close29，
以实际新ends／old counts／predecessors／origins选刚交付J／U，完整canonical $k,z$及sidecar对应，
再测量导出／seal一个NEW actual response state，含全Y和origins。

新hook仅在 mode01、这个实际family sidecar、$c=AfterFinal$、三family cases之一，
且新response state seal之后、第一条原AfterFinal指令之前使能。
RawReturned、Lift、Reserve、Raise均不被拦截；mode10旧hooks保留原固定cases。

**定义 34.2（Wait及整个M）。** hook时A持自己的ports、全pool和RG invocation，dispatcher已持source token。
把该特定NEW response-state reference和原waiting packet分别存入互异持久字段。
新Close29后构造定义21.1的Wait12：family version、captured-state-ref、original-waiting-packet-ref、
sidecar-local-ref、c、old CountsEnds7、new CountsEnds7、SourceBindings4、GuardBinding2、ProposalBinding2、round、I。

在这个固定prefix上用实际pending／completed full-key lists，从J／U／sidecar／packet／Companion／guard／proposal／
boot／prior／description／I／Q／DA及真实previous-receipt依赖作typed backward closure。
只沿声明reader边找本地或equal-origin acquired blocks；不扫任意payload中的“像引用”的子串，
不反向追origin，不查询未来Wait／M／ACK／Done。
M固定前部恰九个B域：

$$
T_9(\mathtt{FAM\text{-}SETTLE},I,\text{actual-Q-key},\text{actual-DA-key},
\text{original-canonical-count3-word},c,oldCountsEnds7,newCountsEnds7,\text{complete-real-Y}).
$$

其后实际 $U(d_{cat})$、恰 $d_{cat}$个五B域catalogue项及exhaustion；项为
$(role,\text{full-origin-or-local-key},\text{actual-A-local-ref},type,\text{complete-acquired-payload})$。
$CountsEnds7=T_7(q,g_c,e,j,m,semantic\text{-}endOption,unified\text{-}endOption)$。
旧M／ACK／Done／carrier链和全部实际跟随字仍保留。
A按真实字程序／测量导出seal M后，才发送 $U(|M|)$、整个M、010。

**定义 34.3（AA全检查、binding及真实ACK）。** AA须为本attempt的delivered／AwaitSettlement，
已保留Q／outbox／真实transportACK／Confirmation。它先逐位backing length-marks、body、全ending，
再按九frame／count／每项五frame及第32节显式数据栈全读catalogue。
完整检查 Q／DA／identity／canonical／operation／RG01／return case／$S_w$／prior receipt／$G_i$／guard／proposal／round，
old／new counters含accepted-Rho e，J15／U18／两独立predecessors／semantic mate／manifest／fences／initial source／boot／prior。
Q及transport与自己真实retained attempt逐位比较；metadata不替代bank位运行关系。

在唯一 $r_0$ driver返回且当前grants有效时分配 $B_i$，逐域写 previous binding-tail、
SAME old-selected descriptor、actual candidate descriptor、request／transport／outbox refs、实收M、全Y／J／U／dependency backing、
从真实Y读到的outcome。seal最后完成，才更新selected：Y1选candidate，Y0保留同一个old descriptor；再链接tail。
不改source edge、root slot或grant。旧和被拒candidate及所有历史／记录均保留。

AA seal $ACK=T_4(\mathtt{FAM\text{-}ACK},I,\text{ENTIRE actual received M},\text{actual outcome})$，
干计数并真实打印 $U(|ACK|)$、全body、010。
A74按定义21.3分别构造真实length／body／ending blocks；body到三ending位全部接收匹配前保持status0。
长度用IN／EX／WR／RD-test／MR至真实0，body用完整计数字逐位IN／WR／推进，ending三位各完整backing／测试。
正确后才status1；完整四frame／exhaustion，比较全I、整个自己的M、恰一位outcome=真实Y，
再检查Wait及特定captured-state／packet／c／两ends。
成功才seal Done8，包含真实Wait、M、ACK三parts和captured-state refs及实际choice。
随后写

$$
T_8(\mathtt{FAM\text{-}RECEIPT},\xi,U(i),\text{actual-J-origin},\text{actual-U-origin},
\text{actual-M-reference},\text{actual-Done-reference},\text{actual-ACK-parts-reference-triple}).
$$

carrier只指已完成对象，不含未来completed-round state或自身未来reference。

**引理 34.4（完整结算及原下一入口）。** 在假设26.2及上述真实返回上，结算有限完成，
所选actual descriptor恰由真实Y决定，随后同一个新response state供应原AfterFinal／Entry。

证明。所有catalogue roots及边均指较早sealed typed objects，full-key completion和第32节双界栈保证有限全parse，
receipt bundle给全实收旧字。逐位send／receive归纳给AA实际M、A实际ACK，完整echo／occurrence检查将其接回本attempt。
$B_i$ seal前已有真实old／candidate refs；选择不能由Plan或预测位代替Y。
A临时工作与captured-state／Wait／carrier各自分离，恢复74保护头距离，原R约定恢复为新Tail74。
再新Close29，按完整reference重载SAME captured NEW response state，不选helper遗留的旧LatestType。
仅此时执行恰一条原AfterFinal：读真正Y更新 $t$／counts／mode／stage，测量导出／seal原完成轮状态，
十二反向TOK回P、恒等角色CTL、实际Tail13／17及原Entry边。
RG invocation一直在原槽，dispatcher已有source token；RG6.2–6.3遂供应下一真实loan／reload／Select／raw ingress／独立guard入口。
下一speculative edit必须等待前一次全settlement／ACK完成。
End／local ACK、PayloadACK、copy-completion TOK、whole-row ACK及settlement ACK各保留自己的角色，互不替代。$\square$

## 35. 实际 Park与完整原 Stop／INITIAL消费者

**定义 35.1（finish前置Park）。** 任意完成mode01 Entry，包括 $N=0$，保留原真实finish选择。
原finish-selection loan／reload后pool已经在A；先按RG9.1导出／seal ORIGINAL HandbackPending，
另存其特定reference，再在原reverse-pool／Handback边前插入固定Park子阶段，不另发起loan。
从last-final origin选唯一当前receipt；$N=0$取initial receipt／lift-final origin。
complete-current-receipt按定义30.2实际取得全载荷／catalogue并全检查，foreign words仍仅为本地实收容器的谱系键。
实际写并seal

$$
Park=T_6(\mathtt{FAM\text{-}PARK},I,SourceBindings4,
\text{actual-HandbackPending-reference-and-full-payload},
\text{last-final-or-lift-origin},\text{complete-current-receipt}),
$$

在互斥settlement方向真实发送 $U(|Park|)$、body、010。
AA仅在settled attempts之间、无pending edit／maintenance／request／output时接受，
完整backing／parse，检查identity／$\xi$／current receipt和final或lift occurrence与retained binding一致。
seal Park record，保留四根、descriptors、source／tapes、attempts／outboxes及settlements，禁用后来arena request入口。
seal $ParkACK=T_3(\mathtt{FAM\text{-}PARKACK},I,\text{ENTIRE actual received Park})$。
最后output边达到FinalPark，因此A收到完整ending时停车承诺已发生。
未用legacy drivers已idle／returned，无pending request，也受backend park抑制。

A按A74完整length／body／ending receiver实收ParkACK，全三frame／exhaustion／whole echo检查后恢复74 heads，
新Close29重载SAME saved HandbackPending；此时才原十二反向TOK及CTL到Handback。
所有连接在完整消费reply后为空；不是把park留到halt之后。

**定义 35.2（原terminal全路线）。** Handback按RG9.1进行另一次新的loan／reload。
从实际保存原字用原configuration／stack grammar作完整copy，在25追加fresh active original configuration，
在27追加initial empty waiting，全reference fields、实测base／length／descriptor／status完成；
保留旧RG／AA states、source／journals／archives，不rollback历史。
按原代码定位table24，归还十二work TOK，恒等角色CTL、Tail13／17，一次invocation TOK到原client，
再原loan／interpreter entry。原解释器真正执行Stop，在31写／seal $(0,B,1)$。
实际terminal output／packet／原instruction／control dependencies经完整49到P21／17，在Halt前完成。

原Halt执行start／commit、J／U及全部dependencies，经48全交付／checks／whole-row ACK；
实际冻结包含Halt的两完整indices／counts／last refs，构造并seal SEG-P1。
其每个request、semantic mate、原boot／initialization／prior／control／output／J／U依赖均实际列出，
经50真实allocation／mailbox／copy／status／seal到verifier32／33，只从已有local copies解析origins。

原verifier在 $H_0=1$枚举全部 $4^{2H_0-1}$初始包，验证prior $\{\alpha,\beta\}$，
分开保留initial-target与replay-current。按冻结顺序完整读每个U及其J／request／control／output，
逐行检查历史guard／layout／Reserve／Raise／manifest、真实operation／response、$q,g_c,e,j,m$、
双predecessors、code／fences／terminal-return-kind。不能只读最新guard，也不把auxiliary字／AA工作伪造为NativeLocal。
原seed beta取得排除initial alpha；每个后续真实原row继续保留actual beta。
因此compatible INITIAL fiber非空且对原 $q_1$恒定，实际构造accepted SEG-R1 INITIAL-$q_1(\beta)$。
receipt creation／seal来自真实完成delivery descriptor，不预写未来seal读数。

expected-task／proposal／frozen-prefix／snapshot／two-end bindings和receipt经原51实际到consumer40／41。
其全字段检查 $\xi,H_0,prior$、proposal／type、两counts／ends、snapshot、accepted receipt seal后，
才在43真实Zero-allocation、逐位target copy／seal／OUT；完成实际acknowledgement、全部规定tokens归还，
最后吸收global-halt CTL。没有以AA成功token或同名receipt替代SEG-R1和真正target输出。

**定理 35.3（停车后的同次原终止）。** 在假设26.2下，从任意上述完成Entry及其真实finish，
定义35.1–35.2有限完成恰一次原handback及INITIAL-$q_1(\beta)$消费，达到吸收global halt。

证明。Entry的真实state／owners／tokens和启动前保存原配置给RG9.1及定义22.1–22.3的共同入口。
Park只做实际paid source-free traffic，完整echo后仍重载同一HandbackPending，故原入口未被代换。
原configuration全copy、表定位及tokens／invocation转交给原Stop入口，不把RG描述当Turing表。
第33–34节供应每个改造final的真实原效果／历史行，其余原calls不变；CAP6.5–6.6的finite verifier
逐行论证保留actual beta，并给完整consumer checks／输出。所有段在其前段真实出口运行。
invocation只离开RG一次，原terminal图无返回RG边，global halt无再入；因此没有posthalt工作或later terminal task。$\square$

## 36. 任意实际到达轮次的不变量与逐点有限完成

**定义 36.1（returned-round关系）。** $\mathcal R_i$表示已经实际到达的mode01 Entry，满足：
Native source为 $E(t_i)$，实际 $h=K=w(t_i)$；原RG state保留完整真实responses／rows／两ends、
saved original client及当前invocation；P持十二work tokens，dispatcher持idle source token；
AA固定 $r_0$ driver全部内层调用已返回，所选真实cone body为 $E(t_i)$，binding tail为 $B_i$；
A有按 $\xi$／round／preceding-final匹配的唯一completed receipt，$i=0$时为 $B_0$及initial carrier。
旧material、当前rights、heads／latches／channels、四根及全部共同ambient histories均在joint state内保留。
这个关系不把它们quotient成body或一枚accept位。

**定理 36.2（任意 $i$的同次一步闭合）。** 在假设26.2下，从任何实际达到的 $\mathcal R_i$，
每个接下来真实供应的合法ordinary raw modifier及独立finite nondecreasing guard，
都沿本构造到达 $\mathcal R_{i+1}$；原final全回应、真实 $Y=\varepsilon_{i+1}$、
两条记录链及selected descriptor均是这一次执行的新出口。

证明。按实际相继阶段证明，不预设下一阶段终点。

1. 原Entry loan／Select／RawWait／RawDispatch有真实token／invocation guards。
   RG4.3适用于tight source $E(t_i)$：未知raw Rho／Left／Right实际执行完整candidate及原refusal，
   $h,K$及源不变；raw rows／request／operand／response安装完成。本hook没有作用于此call。
   RG5.1–5.2随后在实际A69收到独立 $U(g_{i+1})$，写真实descriptor／status，
   新Close29全读并构造 $G_{i+1}$，保持proposal／guard／preceding-final的不同发生。
2. 原Plan只消费现在已经取得的operand、count pair和guard。令旧reference counts为 $(a,b)$，
   原(RG.5)给Rho的reference candidate叶数 $a+2b$、encoded目标 $3a+5b$；
   graft给reference叶数 $a+b+n(v)$、encoded目标 $w(t_i)+w(v)$。
   两者encoded目标严格大于旧 $h=K$。若reference whole-candidate满足 $g_{i+1}$，
   完整执行原strict Reserve(d)及Raise(d)，各自全return／state安装；否则不维护。
   维护改变actual backing／guard／layout／unified历史，保留selected Native和AA body；
   其后真实 $h$才用于第30节尺寸，绝不读未来输入。
3. 实际ComputedWait／Companion／canonical／F7／Assoc／唯一start-fence／Q writer，
   给第29–32节每个真实入口。fresh cone前缀不可比、birth checks及sealed old-frontier构造literal candidate；
   全新Tag／outbox、五帧IN-WR、28／8／10及全nested／stack readers给本次bank和实际后置BIND。
   旧selected descriptor保留同一对象；共享祖先tapes只作真实追加。
4. 引理33.4的全原parser／MUX／ordered STORE／release给真正Y。
   若原Plan维护，candidate为 $E(c_A(t_i))$、叶数恰actual $h=d$，故真接受；
   若不维护，candidate叶数 $d>$旧 $h$，故真执行拒绝。
   RG(RG.2)遂给 $Y=\varepsilon_{i+1}$、source $E(t_{i+1})$及tight $h=K=w(t_{i+1})$。
   Plan位从未直接写response、源或AA choice。
5. 第34节实际选择operation-dependent counters，写全J／U／indices／sidecar／dependencies，
   完成全receiver checks／WHOLE-ROW ACK／source TOK／idle后才新response-state seal。
   全M／ACK／Done／carrier使 $B_{i+1}$仅由真实Y选candidate或SAME旧descriptor。
   重载同一个captured NEW response state，原AfterFinal／反向TOK／Entry边给下一 $\mathcal R_{i+1}$。
   每个history／receipt依赖只指已完成过去，下一调用尚未运行。

所以此一步对任意已到达 $i$成立，不只对一个预先枚举的后续stage成立。$\square$

**引理 36.3（所有新增循环的有限进展）。** 在假设26.2及任意有限已完成前缀上，
本构造新增的每个合法完整phase都有限返回其规定出口。

证明。receiver／echo消耗实际finite marked lengths；descriptor／association扫描冻结输入count。
ReadBody栈遍历有限stationary树；Build帧消费有限input tree的proper subtrees，每次AA调用由AA20.3完整返回；
rho消费编辑前封存的有限frontier，输出／PAD循环消耗actual finite word／capacity。
原forest的E孩子严格更早，FEND固定Q，原frame machine按定义6.6终止。
full typed parser或者缩短inline span，或者访问frozen有限INPUT集合中尚未completed的key，
自己的STACK输出不扩展INPUT界。每个receipt／catalogue在 $i$归纳下有限，即使嵌套字长迅速增长；
current receipt不含自身future carrier／Done／descriptor。原计算／ingress／ACK的进展条件仍由假设26.2供应。
连接的receiver在相应send阶段已就位；每次ACK只依赖刚完成输入及已有backing，没有等待未来round的数据环。
所以材料供应、完整输入、规定确认和原计算终止之外，没有另添一个假定的join-progress条件。$\square$

**定理 36.4（完整ordinary域的一boot有限完成）。** 存在定义27节这一个固定有限原始安装，
在假设26.2下，对定义26.1整个输入域——含 $N=0$、任意有限mixed schedule、任意实际非空有限operands、
独立nondecreasing finite guards和依先前acquired responses作的选择——均有本构造的有限完成：
每个selected final由实际arena candidate供应，保留完整原service／response／records／return／Entry，
最后实际Park／original Handback／Stop／INITIAL consumer output／ACK／tokens／global halt。

证明。引理28.4给 $\mathcal R_0$；定理36.2按实际finite returned-round序列归纳，
每一步量化的是前一whole response／settlement之后才真正供应的下一输入，故允许声明的online adaptive选择。
引理36.3在相同执行的每个入口给逐点finite completion；到 $\mathcal R_N$后，定理35.3给真实finish后缀。
所有存在对象都来自这一个boot、同一 $\xi$和前段实际出口。$N=0$用initial carrier及原finish，不虚构任何final。
安装的port／type／driver／return-case数不随 $N$增加；数据与retained material可以增长。
例如每次真正接收Right(alpha)、$g_i=i+1$的任意长有限运行均accept，$w(t_i)=3+2i$；
任意大operand的覆盖来自上述一步量词，非这个特殊例子。
没有finish或未供应完整ingress的执行只有实际前缀，不能从本定理推出有限terminal或实际无限运行。$\square$

## 37. 原 mode10的准确保留与行为标签

**命题 37.1（legacy分支的原域）。** 在假设26.2下，本安装的mode10分支保留定理23.2及22.4的
全部所声明finite guards和原Stop／INITIAL完成，使用actual新身份／地址／fences，但不扩张其policy域。

证明。backend选择legacy之后，执行原三固定driver、$O$七事件、原Native boot／Lift／C0／C1／C2图。
$C_0$实际guard2后，C1 Left的真实候选 $F=\langle C,C\rangle$；C1 guard2选O、guard4选F。
只有C1全结算／ACK／captured-state reload／原Entry之后才构造下一operand并接收C2独立guard。
C1拒绝时C2为Right(alpha)，guard2拒绝、所有finite guard至少3接受；
C1接受时C2为Rho，guards4、5拒绝、所有finite guard至少6接受。
保持第23.1节的完整维护、F7 typed marker／referent／holder、28／8／10读取、原程序／rows、
两个全settlements、原FinalPark／Handback和完整terminal route。
新增 $r_0$在此分支未请求且保持真实alpha／idle，作为distinct framed source保留，不能认同O／F／N。
因此旧theorems在这个更大安装的实际对应入口适用；全部费用在新入口重算，不复制旧常数。
这不是从mode01归纳推出任意internal policy。$\square$

**定义 37.2（原操作、拒绝与非执行状态）。** 全七canonical bodies ReadE、TagRead、Rho、Left、Right、Reserve、Raise
及原journal入口仍resident，保留原guard与source-token意义。raw staging不替换candidate materializer，
maintenance保留strict／unchanged／maintenance-refusal的不同cases。
family hook仅作用mode01的selected computed finals及原固定mode10 hooks，
不宣称任意七tag direct schedules或离开所声明controller域后的同步。

accepted、executed source refusal、maintenance unchanged／refusal、完整合法非modifier的controller-domain exit、
frame-fault、adapter FaultHeld、busy或missing-right的disabled none、partial ingress／status0、absorbing terminal均保留不同状态／后继。
强制field／holder／grammar／transport错误按定义6.7、18.6耗费实际剩余预算排空、记reason、FaultHeld，
不伪造Y0／rows／settlement／Entry；已有较早真实提交不rollback。缺输入只保留pending prefix。
真正guard拒绝则完整通过decoder、执行全部MUX／STORE／release／records／return。

**定义 37.3（full joint state与权限边界）。** 在每个cut保留Native私有coordinates、raw STORE prefix、
AA真实parent／全部共同ancestor tapes、alias／source／call／creation identities、partial buffers、
rights、finite controls、heads／latches、meter及费用。
本文对应是声明的body／原标签／入口关系，不是旧／新microtrace、引用、cost或arena／disconnected-root行为相等。

AA仅由owner及固定driver创建／编辑／read／Maintain；descriptor数据不创grant。
P独占bank／Input22／F7／forest及private解释，A拥有saved client／state／receipt和全return checks，
原verifier／terminal consumer保留原权限。foreign key只选已实收payload；没有reference-bit cast、remote dereference、
A／AA私有source16读取、per-round安装或清除强制backing。
RG-I／J_IC102是不同安装，其actor interval reader／emitter省略active payload-bank重建；
本构造省略PRODUCER selected candidate scatter。两种省略不合并计新成果，
IR既有current-capture／return结果不按同端口名自动覆盖本arena／decoder／settlement／Park内部。

## 38. 同一次实际执行的全费用递推与可核对子计数

**定义 38.1（实际出口上的向量）。** 将完整日程展开为同一实际执行
$z_0\xrightarrow{\kappa_1}\cdots\xrightarrow{\kappa_M}z_M$，
每个原语在其实际前态按Native／AA原tariff贡献独立坐标 $\delta(\kappa,z)$。
保留按owner／purpose／opcode的Native次数、ticks／fees／receipts、ordinary construction、
code／control／type／token／connection物质、定位／head移动、各direction wire、真实descriptor／unary／reference位；
AA分配／grants／fields／tests／I-O／ACK／control／reference-bit costs另列，不设任意兑换汇率。

$$
V(z_r)=\delta(\kappa_{r+1},z_r)+V(z_{r+1}),\quad V(z_M)=0,\qquad
P(z_r)=\max\{S(z_r),P(z_{r+1})\},\quad P(z_M)=S(z_M).
$$

组合严格为 $V(A;B,z)=V(A,z)+V(B,exit(A,z))$，peak取实际连续prefix的同时retained材料最大值。
每后段在前段新实际出口计算；ordinal／地址／fence／type／reference宽度／nested receipt长度均动态改变。
闭合fence只读旧cut，其后读数动作本身的receipt仍计费，不解自包含费用方程。

Native十原语 RD／WR／ML／MR／EX／BF／IN／OUT／TOK／CTL的实际发生数为 $n_N$时，
沿CAP／AS约定 receipts、ticks、fees分别为 $n_N,n_N,2n_N$，material为
$S_0+b_{control}+8A_{nonmeter}+8n_N$；已作为格计入的code不重复计。
这是坐标公式和展开程序，非已测whole-run数字。

全程段包括：四根／drivers／links／types／描述／identity及public copies，Native boot／saved client／Lift，
Init／first cone／InitACK／initial carrier；每轮原choice／raw ingress及完整raw materializer／refusal／return，
独立guard／state／Plan／两次可能maintenance；Companion／actual旧receipt全复制／packet／canonical／F7／holder／Assoc／
old fields／prepared increments／manifest／start fence／Q；fresh cone／全部Build／frontier／Tag／真实祖先Maintain／outbox；
五帧／bank／DA／Input22／28-8-10及全nested stack／BIND／forest／frames／code／all-arm解释／STORE／cleanup／release／commit；
原counter／J／U／indices／sidecar／所有48依赖／checks／ACK／source TOK／idle／新state；
Wait／全catalogue／M／binding／完整ACK／Done／carrier／SAME-state reload／原AfterFinal／Entry；
最后Park／ParkACK、原配置复制／Stop／Halt／snapshot／50／verifier／receipt／51／consumer／43／OUT／ACK／tokens／halt。
每Raw／full scan／comparison／At／Last／Home／Tail／status／seal／role CTL及TOK都按实际recipe展开，未给helper单位价。

**命题 38.2（源调用与arena定位子计数）。** mode01从seed后到terminal前的原Native source／maintenance calls数恰为

$$
4+2N+2N_{accept}.
$$

令 $m=N+1$为初cone及每个final candidate cone总数；$P_j,S_j$计cone $j$内部全部成功P／S，
$D_j$为这些事件的relative-address depths之和，包含Build及rho编辑。则

$$
\begin{aligned}
P_{ar}&=1+\sum_{j=1}^m P_j,&S_{ar}&=m+\sum_{j=1}^m S_j,\\
D_{ar}&=\frac{m(m-1)}2+\sum_{j=1}^m\bigl(j(P_j+S_j)+D_j\bigr),&
V_{ar}&=1+P_{ar}+2S_{ar}.
\end{aligned}
$$

arena tape headers恰 $S_{ar}$，routing cells／side appends恰 $D_{ar}$。
mode01仍保留legacy $O$的3P／4S／depth sum7／12source vertices，$F,N^*$各一untouched alpha vertex；故四根合计

$$
P_{tot}=P_{ar}+3,\quad S_{tot}=S_{ar}+4,\quad D_{tot}=D_{ar}+7,\quad V_{tot}=V_{ar}+14.
$$

按AA22.1，四initial roots的located source parent／child assignments恰
$12+4P_{tot}+8S_{tot}$；located auxiliary assignments恰 $V_{tot}+3S_{tot}+4D_{tot}$。

证明。四Lift、每轮raw和final、每accept的两strict maintenance给call数；auxiliary Init／AA／word／settlement／Park
不创造Native source或NativeLocal事件，却各有实际primitive receipts和分配。
scaffold初始一次P，取得 $m$个cones用 $m$次S，其global depths为0至 $m-1$。
cone $j$根depth为 $j$，内部depth $d$事件在全源depth $j+d$，所以深度和恰如式。
AA每P增加一source marker、每S增加二source vertices及一header，每proper ancestor恰追加一tape cell。
旧O七events和另两roots给额外14vertices／7depth，四initial roots贡献12source初始化fields。
其余located assignment由AA22.1逐事件相加；公式明确不含allocation／grant／navigation／tests／I-O／scratch／引用位费用，
不是total tariff。mode10则取第24节actual三root子计数，另加untouched $r_0$／driver／boot footprint。$\square$

**定义 38.3（完整字长、wire及复制项）。** 对实际 $r_7=T_8(a_1,\ldots,a_8)$、Input22字段 $f_j$，
有 $|r_7|=\sum_{1}^8(2|a_i|+1)$，$|Input22|=\sum_{1}^{28}(2|f_j|+1)$。
Rho marker payload／sep／status恰3格，holder为 $|r_7|+2$格，field7各快照亦 $|r_7|+2$，
另外付全descriptor／reference／component snapshots／Assoc／Kcall／stack及旧versions。
28外pass每遍全28frames，第7frame实际读28次；另八全reference reparses、十全descriptor passes、
所有association prefix scans／holder全比较／unary算术／status／payload validation，不折成单位lookup。

global depth $d$的P／S请求恰 $4+2d$wire bits，Growth payload reply恰 $5+2d$，
End／ACK／Return和所有Tag／path／reference／ancestor work另计。
$q_Q=|Q24|$时五外帧分别为

$$
2q_Q+8,\quad2q_Q+8,\quad2q_Q+c_{\rm cap}+2L+10,\quad
2q_Q+L+9,\quad2q_Q+L+9,
$$

总 $10q_Q+c_{\rm cap}+4L+44$；端点print／receive／backing／echo／parse／allocation／status另计。
M九固定域 $u_s$、$d_{cat}$项 $w_{t,s}$给

$$
\ell_M=\sum_{s=1}^9(2|u_s|+1)+(d_{cat}+1)
+\sum_{t=1}^{d_{cat}}\sum_{s=1}^5(2|w_{t,s}|+1).
$$

M wire $2\ell_M+4$、Native send核心 $8\ell_M+13$；ACK长 $a$时wire $2a+4$、Native receive核心 $10a+27$。
完整allocation／position／descriptor／seal／四域parse／whole-M echo及AA端工作另计。
Init／Park按其实际 $B/T$字长和真实framing计算，非单位handshake。
每48／49长度 $k$copy保留两循环／seal／TOK核心 $12k+6$、四全池handoffs的52原语，
并加所有setup／Base／Zero／descriptor／status／position／check；whole-row ACK／source TOK／idle另列。
50／51／output完全采用原展开，不能由这一个核心项代替。

每实际gate的 $v=(a,b,c,d)$和seek前head $h_{G,r}$仍给原PR57.06

$$
I(G)=18+5\sum_{r=1}^4(v_r+1)+\sum_{r=1}^4(2h_{G,r}+3v_r+3)+5+P_G,
$$

$P_G$具体展开cache descriptor／seek／Home／Last／At／status／control；generation、terminal RD／exit、
allocation／cleanup／response／rows／return另计。J／U全长为各15／18域的 $\sum(2|field|+1)$。

**定义 38.4（保留material及价格边界）。** peak包括original source／backing／archive及全部STORE效果，
所有bank／state／code／counter／journal／index versions、mandatory T或marker／holder／association／snapshots，
AA四roots／source vertices／headers／tapes／真实parents、选中及拒绝cones／descriptors／creation records／
旧body与candidate acquired words／frontier／stacks；Init、每个Q／DA／outbox／full reply／M／ACK／Done／carrier／binding，
recursive旧receipt全copies、connections／latches／length marks／parser cursors／reserved material／saved continuations，
原terminal snapshots／replicas／receipt／output和全部code／control／type／token births／真实宽度references。
清scratch不退还已构造capacity。共享spine变深、重构和嵌套全receipt可以增加费用。
以上提供complete same-run recurrence及明确located subcounts；没有total-resource saving、polynomial bound、
latency／throughput、统一有限hardware／time、physical price、efficiency、全资源支配或global／Pareto minimum结论。

## 39. 可区分的有限前缀与反驳判据

**定义 39.1（有限discriminator）。** 在同一mode01 boot实际依次选择
Right(alpha)、Right(alpha)、Rho，独立参考guards为1、2、4，然后finish。
按原whole-candidate法：第一raw和第一selected final均拒绝；第二raw仍拒绝，第二final接受；
Rho的旧源必须是第二轮真正接受的后继。
相同family type和重复Right(alpha)字不能使Kcall、call／Companion／guard／J／U origins相同；
真正Y0／Y1必须分别保留旧descriptor／选新candidate。这里规定一个source-level区分例，未提供其执行记录。
它不能替代定理36.2对任意 $i$的证明。

在已编辑另一个cone后，直接检查旧candidate的非null parent及 $r_0$真实ambient tape，
可区别shared arena与independent roots；把这些当null／不变即违背AA的实际维护关系。

**定义 39.2（足以反驳本构造的具体义务失败）。** 任一合法实际前缀若出现：
Kcall association缺失或选旧holder、beta-born构造需非法P、遗漏真实parent／tape更新、
bank位不是该actual outbox、被删scatter仍是live fallback、Y0改变selected descriptor、
任何mandatory local／public payload或token／whole-row ACK／settlement return缺失、
Park／Handback未供应原Stop／INITIAL入口，就反驳相应构造义务。
有限witness可反驳，有限passing fixture不能证全域；上述区分前缀及较大树例没有被当作fresh验证证据。

## 40. 精确来源对应、新增接合与剩余全目标

**定义 40.1（固定primary sources与适用前提）。** 本增补数学原文统一钉在
`7785ec6df54bf056b0b59bdbce76664c3ba7777e`。下表按原编号给来源；
本卷第1–25节仍以各自原编号／原表述使用，不改写它们的字节或原范围。

| 原来源／编号 | 本增补的精确对应及限制 |
| --- | --- |
| [AA17.1–17.3、19.1–20.3、22.1](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | 四真实allocator根、出生类型构造、非Next服务的全生命周期、全祖先routing tapes、located counts；cone只是在固定 $r_0$内的真实subtree |
| [LAB9.1、9.3–9.4、11.2](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) | 整个 $\mathcal D_+$的sealed old-frontier literal rho及finite serial service已存在；本增补只用prefixed原driver实现，G不是literal Right |
| [RG1.2、2.1–3.3、4.1–5.3、6.1–7.3、8.1–9.2、10.1](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md) | 实际beta／saved client／Lift；未知raw全refusal／operand acquisition、独立guard／G、原Plan／computed return／Entry；同次original terminal；(RG.2)给encoded candidate law，非新代数 |
| [AS1.2–2.6、3.3–3.5、5.1–9.6、13.1–15.4、17.1–23.3、24.1–25.3](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION.md) | 原Raw／pack／十二字、five frames／bank、forest／frame／Emit／full parser／STORE、真实rows／settlement／terminal算法；本增补实际供应可重复occurrence／reader／entry；mode10仅原C1／C2域 |
| [CAP1.2–2.3、3.5、4.1–4.6、6.1–6.7](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md) | 原七service／stable injective $\phi_K$／canonical count3、八reference／十descriptor／fence、全J／U／copy／ACK、历史verifier／INITIAL及原consumer |
| [TMC PR57.D1、D4、D5、L3、T1–T2、.06–.10](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | 原primitive／literal gate／parser／whole-candidate scatter及MUX语义；仅选中final scatter删除，fixed-H内部policy不并入独立guard域 |
| [ARC2–3、16.2、26.2–28.1](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md)；[RCA11.1–12.1](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md) | finite word／list／unary、双bank、实际测量export／protected import／packet／configuration copy；parser stack为数据，static helper图不递归 |
| [IR1.2–1.4、7.1–8.2、24.5–26.4](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMMUTABLE_INTERVAL_REGISTERS.md) | 另一安装的actor重建省略、compiler-cut取得及边界；不作为本新图内部current-capture theorem |

[NativeFullSourceProducer.sourceControl／native_source_producer](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean)
及其同名Blueprint Scribe阐明stationary acquired-reply stack traversal，前提是已经供应其Native register接口；
它不产生AA grant、bank entry或later-task handoff。
[SameHandleContinuation.SourceService／Completion／continuation_exists](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.lean)
显式假定bound service、fixed handle和completion，不能代替本构造的实际handoffs。
[TypedFiniteViewKernel.response／refinement／typed_finite_view_kernel](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean)
及其Blueprint Scribe要求真正typed steps、完整labels／readout／legality，不供应本图新Q kernel或quotient。
这些是源码含义／复用边界，不是本增补的新compiled applications。

**命题 40.2（旧25.3的精确新增部分）。** 定理36.4补上旧25.3未由固定两stage构造供应的这一部分：
一个新原boot，先真正接合自己的Lift与初始arena selected source，
对全部ordinary mode01 finite rounds的每个selected Rho／Left(v)／Right(v)，
实际operand-driven fresh candidate、发生键关联的F7／holder／Input22、可变深度完整旧receipt读取，
完整原bank／program／rows／Y-linked settlement／receipt／Entry和preterminal Park／original INITIAL consumer。
不对固定旧J加later stage，不把已用O／F／N重当fresh，也不扩大mode10。

证明。第28节提供原始join，第29–32节提供每次真实source／operand／reference／bank／decoder入口，
第33–35节提供原效果、真正return／settlement／next-entry及完整terminal，
第36节以任意attained $i$归纳而非有限stage枚举将其组合。每段同一 $\xi$且在前段actual新出口执行。
具体新增是这一boot到原消费者的可重复操作接合；AA出生构造／真实tapes、LAB rho／serial algorithms、
RG原caller／Plan／Entry、AS writer／parser／STORE／row／settlement、CAP verifier及ARC／RCA字程序均为复用。
没有把重新叙述这些算法、同值编码或actor interval omission计作新基础。$\square$

**定义 40.3（保留的准确未决范围）。** 较大的RRO最简关系／四表达互恢复目标未由此完成。
本新arena／supplier／decoder／settlement／Park内部，无需等待未来原完成的immediate／current reentrant acquisition仍未供应。
[RCA15.3](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md)
已在其同一expanded graph及canonical-frame域内给finite-completion-conditional later Cover、真正immutable取得及exact historical Call，
包括旧handler／compiler／descriptor／ingress／copy interiors；该历史closure不重列为未解。
它不自动给本新图任何忙碌cut的当前可请求入口。

[GENERAL15.5／18.4](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md)
分别已覆盖同一actual Ready $P$后的unchanged-original-row source-only01 rolling／cross-entry cuts，
以及所声明successful mixed histories的指定final post-IN／pre-EX13 cuts；
[RG13.3](https://github.com/the-omega-institute/trureturing/blob/7785ec6df54bf056b0b59bdbce76664c3ba7777e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md)
已覆盖inherited non-IN charts上的声明mode／round original-Q分离。
尚缺的是超出这些域的changed／new rows、broader mixed interiors及full terminal-task kernel，
不是把所有cross-entry原Q结果一概判为空白。本构造也未供应all-cut四个独立可用表达及其全部原消费者。

任意internally generated independently guarded policies、任意all-seven direct schedules、
更广generic source族／非canonical物理源、实际无限执行、统一有限设备／资源、
任意later terminal task／current target转换、total-resource advantage和global／Pareto最小性均未由此给出。
原INITIAL始终为同一次准备的目标，没有posthalt reentry。
其他新geometry／minimality结果不充当这座操作桥的证明前提。

**文献表态。** 本增补是以上仓内来源的具体综合推导，归属为repo-derived；
未作外部文献穷尽核查，不主张全球原创性。证据层次为有明确材料／权限／输入／原计算条件的普通source-model构造与归纳。
本文没有提供已执行示例、新Lean／exact-S编译、公理闭包核验、physical conformance或实测whole-run费用；
源码既有证明及其接口含义不能提升为这一个新组合的kernel验证。

## 追加锚（本行以下为增补区）

## 41. 独立请求入口与真实ACK的当前捕获合同

本节至第44节研究第40.3节尚缺的current acquisition的一种机制类障碍。
第26–40节的ordinary family构造、原mode10范围、原source／consumer及费用合同均按原条件复用。
记本节的安装为 $B$；它有自己的真实boot、description、identity和原始准备 $\xi$，
不因端口名称、body相等或可编码性而与另一个安装认同。

**定义 41.1（保持全目标的当前请求规格）。** 普通输入域仍是定义26.1的全部量词：
安装先于每个有限 $N\ge0$、每个实际adaptive Rho／Left$(v)$／Right$(v)$序列、
每个在原raw ingress真正收到的非空有限有序operand、独立收到的有限
$1=g_0\le\cdots\le g_N$及finish；mode10仅保留定义26.3、命题37.1的准确域。
返回Entry时的 $E(t_i)$、$h=K=w(t_i)$、真正Y及arena selected body关系沿用定义26.1，
完整原service／refusal／records／AfterFinal／Entry／Park／Handback／Stop／INITIAL consumer沿用第33–37节。
这个普通域不是只在若干测试输入上成立的合同。

设 $e_B$ 是真正完成capture-support边界构造、代码／owner／slot安装、bank初始化之后的
固定EnableCapture CTL，先于首个覆盖的J-FAMILY runtime过程。
原private preparation、未取得seed／code及pre-enable范围仍分开。
在 $e_B$之后、absorbing halt之前，要求覆盖每个实际到达的primitive boundary：
Init、arena allocation／Build／old-frontier rho／navigation／ancestor maintenance、candidate observation、
transport、F7／holder／occurrence association、Input22、variable-depth decoder、forest execution、
settlement／receipt及Park，以及所有新增request／spill／logger／copy／decoder／ACK／return过程内部。
这些过程及capture自身的内部都允许任意有限次数、任意有限深度的nested requests。
域按实际过程和boundary给定，不按handler是否已经使能、对象是否完成或busy flag删减。

请求在一个这样的cut提出时，须有使用其自身合法有限traffic的有限admission／acquisition路径，
不能先执行所悬置的原pending action来取得入口，也不能等原过程未来完成。
冻结目标是该请求在首次capture side effect之前的实际admission prefix；
子请求必须接回那个partial parent的同一个owed action。
即使该action已经使能，仍须先服务当前子请求，再把它作为同一个pending consumer返回并恰执行一次；
若原action缺输入，则返回后仍等它自己的输入。
请求traffic的实际发送、backing及其它副作用各在自己的真实prefix计入，不能被当成无状态的意图。

目标数据含完整实际有限历史及raw joint endpoint $X$，包括定义37.3的全部Native／AA状态，
当前PC／code／heads／latches、真实cell与allocator identities、source16及partial STORE、
AA roots／parents／children／headers／共同ancestor tapes／unfinished reserve与append，
tokens／invocation／partial loans、每条连接的endpoint／空满／位／backing／pending sender与receiver，
status0 bank／partial descriptors、真实call／guard／receipt键、parser frames、分别冻结的INPUT界与演化的STACK界，
未完成settlement／output／Park、所有已发生records和实际费用；不填入未来完成字段。
四个独立取得的space／time／boundary／memory body须各自恢复同一目标，并有各自source解释；
其中实际选中的received body须供应真实continuation的返回。
RG27.1–27.3的四image数学按自己的原安装使用，不由四个codec名称自动取得本新图的对应。
下文的否定结论在admission处成立，无需假定这些body已被构造。

**定义 41.2（机制类 $\mathcal K$）。** $\mathcal K$ 由以下六项操作条件同时定义。

1. $B$是先于未来输入、horizon和capture depth的有限description，含有限ports、literal Native／AA rows、
   typed connections和实际grant／owner／slot初始化，并保持定义41.1的完整ordinary合同。
   新边界以原one-cell EX构造，literal code／control／token bits逐位安装，bank／descriptor／status按原程序完成，
   随后才有 $e_B$。允许任意有限数量的额外ports、rows、channels、grants、roots、finite control cases，
   以及运行时任意增长的有限backed stacks／logs／versions。
2. 新capture的消费／admission通过指定Native request ingress $\gamma$ 的真实input row发生，
   后接实际安装的Native控制。AA可以back／forward请求，但不改这个Native executive的PC或替它执行rows；
   没有能在它被阻塞时独立admit并完成该Native capture的executive。
3. ingress保持typed且分开。每个capture有至少一个真实供应的ACK，由某个
   $\alpha\ne\gamma$ 的literal Native $\mathrm{IN}_\alpha$ 接收；允许任意有限framing。
   它不是wait-any或callback；child request不能冒充parent ACK，即使位值相同。
4. primitive前后及capture内部可插入实际cooperative hooks，进行spill、log、head保存／恢复、token loan及有限分支。
   但一旦到达literal $\mathrm{IN}_i$ row，下一个Native occurrence就是它。
   外actor、queued request或到来的 $\gamma$ 位不改这个PC；没有外部PC rewrite，
   也不把已到达的blocking row原子替换成polling row。
5. 环境可以暂缓parent下一 $\alpha$ 位，同时在 $\gamma$ 提供完整child request，
   并在实际到达其各自合法stage时供应child后续data／ACK；不要求先供应parent ACK。
   这不要求两个不同origin的ACK同时占同一连接。parent ACK不在boot自动预供，也不由omniscient proxy替代。
   每个执行的IN消费其自己的ingress上具有实际protocol origin的真正下一位。
6. advertised domain包括每个新增handler的pre-$\mathrm{IN}_\alpha$ boundary；
   child返回前保持parent的owed action。busy flag不能把该boundary移出all-cut任务。

这里没有“ACK在接收前必为空”或“sender必须等receiver到行才OUT”的条件。
真实sender允许提前执行OUT并填满连接；该执行和位属于 $X$ 及其历史。
有限polling／word-copy／checkpoint wrappers配独立ACK入口属于此类；空间和log规模不固定为某个常数。
in-band request／ACK multiplexer、已证明owner／suspension／return桥的独立capture executive、
nonblocking availability接口、interrupt或外部PC改写不在本类。
这些是比较类的限制，不是对一切合法增广的限制，也不是把整个研究目标改成只研究本类。

## 42. 保持owed row时的控制不变量与缓冲位

**引理 42.1（不执行owed IN时的固定row）。** 任取 $B\in\mathcal K$，
任取一个真正到达的有限joint prefix $H$，其终态 $z$ 满足
$\operatorname{PC}_N(z)=q$、$\operatorname{row}_B(q)=\mathrm{IN}_i$。
对每个从 $z$ 出发的合法有限extension，只要该owed $\mathrm{IN}_i$ 不执行，
Native PC始终为 $q$，没有该executive的其它Native occurrence，特别没有
$\mathrm{IN}_\gamma$ admission，其中 $\gamma\ne i$。
结论不要求 $i$ 连接为空，也不要求该IN当前disabled。

证明。TMC PR57.D1／(PR57.03)把opcode、ingress和successor固定在当前literal row。
在 $q$，该executive的首个可能Native occurrence只能是这一个 $\mathrm{IN}_i$；
RD、WR、TOK、CTL或 $\mathrm{IN}_\gamma$ 不是从 $q$ 可选的另一条row。
若一个extension含该executive的Native occurrence，取第一个；在它之前只有其它actor的occurrences，
由定义41.2第2、4项，它们不改该PC，因此这第一个仍必须是 $\mathrm{IN}_i$，与保留owed action矛盾。
等价地，逐个对其它actor的occurrence归纳，PC均保持 $q$。
其它actor可以改自己的control、backing、meters或连接空满；这些变化不被断言为零。
第2项要求Native admission经 $\gamma$ 的指定row，所以在此extension内也没有child admission。
若 $i$ 位缺失，IN本来就不能执行；若位已存在，IN虽可能使能，保留owed action的extension仍不能取它。
两种情况服从同一个首步论证。$\square$

**命题 42.2（sender OUT保留的两种pre-IN状态）。** 在引理42.1的实际cut，
下列两种真实状态都适用其结论，不能把它们的joint endpoint或bill认同。

| 该cut的实际连接状态 | 必须保留的sender／receiver事实 | 不执行owed IN时的结论 |
| --- | --- | --- |
| 下一ACK位尚不可用 | 实际未完成的sender／input阶段、现有backing、控制及此前费用 | 无Native request admission |
| genuine ACK位已由绑定sender OUT且连接满 | 该OUT occurrence及其origin、sender新control、buffer位／full标记及实际费用；receiver尚未执行这个IN | 同样无Native request admission |

证明。定义26.2只要求sender在空连接OUT，随后receiver IN并完成规定backing才开放下一位；
它不要求OUT紧邻IN。定义27.2将空满、latch、backing和subphase作为实际状态。
故第二行可以是完全合法的已到达前缀。两行分别直接用引理42.1，不使用跨运行交换律。
例如在允许sender OUT的同一prefix $G$后，真实 $G;\mathrm{OUT}_\alpha(b)$
多出一次发送及其全部效果；把它改成 $G$不是保持完整joint prefix的操作。
“receiver尚未消费”不推出“sender尚未发生”，也不取消sender的receipt／tariff。
满连接的父路线可以按原IN继续；这里阻断的是先保持该IN而服务child的路径。$\square$

## 43. 以实际parent历史取得的深度二障碍

**定理 43.1（整个 $\mathcal K$ 的current reentrancy障碍）。** 对每个固定有限、
future-independent的 $B\in\mathcal K$，即使授予它成功完成的实际paid enable prefix，
它也不满足定义41.1的全cut／任意有限nesting／selected-body exact-return合同。
具体地，或者一次覆盖域内的初始capture在自身合法有限traffic下已无所要求的有限完成，
或者有一个真正到达的有限parent-handler prefix和一个child request，
该child在保持parent同一个owed ACK receive时没有合法admission路径。
后一见证只用parent和child两层；不需要无限执行或统一finite-resource／latency界。

证明。固定任意这样的 $B$。由ordinary保留及enable范围，取其 $e_B$之后首个覆盖的
Init／runtime entry的实际prefix。在该处提出parent capture，并按协议在各合法stage供应它自己的有限traffic。
若所需finite completion不存在，第一种失败已经成立。
否则取其中一个真实有限successful parent执行 $F$，含其实际boot及此前ordinary prefix。
这一步只使用假设的capture成功；没有假设一个新的snapshot或busy-owner入口已经可构造。

由定义41.2第3项，$F$中有真实接收该parent ACK的literal Native row。
取第一个这样的接收occurrence，设其位置为 $r+1$、当前row编号为 $q$，
$\operatorname{row}_B(q)=\mathrm{IN}_\alpha$，其中 $\alpha\ne\gamma$；令

$$
H_* = F\mathbin{\upharpoonright}r,\qquad
z_* = \operatorname{exit}(H_*),\qquad
\operatorname{PC}_N(z_*)=q.
$$

$H_*$ 是 $F$的真正前缀，故 $z_*$确实到达，且处于新增handler的pre-IN boundary。
它在定义41.1及定义41.2第6项的域内。
保留 $H_*$ 的所有实际operations、allocations、polls、bodies、copies、records和费用。
尤其，若 $F$在此IN之前已有genuine ACK OUT，则该OUT仍在 $H_*$中，连接仍为其真实full状态，
sender保留它已到达的control及backing；不删发送，不重排 $F$，不选择一个声称与它同态的缺ACK运行。
若此cut的ACK尚不可用，也直接保留这个实际状态。后续论证不以空满作前提。

现在在这个boundary提出child request；按定义41.2第5项提供它的完整frame，
后续child data／ACK只在各自实际合法stage供应。
“完整提供”不表示把整frame同时塞入一位连接，也不表示把child ACK提前放入parent的full连接。
若offer／forward本身已发生其它actor的OUT或backing，取其真正连续extension并保留这些新效果，
不把它的 $X$ 或bill与 $z_*$认同。引理42.1对所有这样的finite extensions仍成立。

这个child的实际pending consumer是parent那一个尚未执行的 $\mathrm{IN}_\alpha$。
定义41.1要求在不先执行它的条件下admit child，取得所要求的目标并返回同一个action。
应用引理42.1，在保持该action的每条合法有限extension中Native仍在 $q$，
不能到达 $\mathrm{IN}_\gamma$，所以没有所需admission。
即使parent ACK已经full而IN使能，先消费它仍先执行了被要求保持的owed action；
后来的capture不能当作这个pre-IN请求的exact continuation。
正确的body、state backup或decoder也不能单独改变live PC。
这给出第二种失败，并与假定的全cut合同矛盾。

最后一次poll若在 $q$之前已答“继续”，$H_*$真实保留该poll；
在其后提出的child不能追改这个answer，pre-IN cut也不因此离开域。
任意有限额外polls、ports、logs、stacks及boot material均不改变引理42.1。
整个证明固定任意 $B$后才从它自己的successful parent选前缀，没有针对未来depth安装代码，
也没有要求每个ACK schedule都呈现空连接。
普通外围可以选定义26.1允许的 $N=0$，保留原初始化及后来的finish意向；
失败在finish之前的一个有限cut已经发生，不要求把不可能的child completion写成已完成ordinary run。
因全规格量化所有有限ordinary schedules和所有有限nesting，存在这一个失败便足够。
它没有把其它 $N$、operands、guards或mode10移出原目标。$\square$

**推论 43.2（存储与表示不能替代这条控制边）。** 即使再给予 $B$在 $z_*$的完整正确state数据
和四个各自正确的public decoders，定理43.1的admission障碍仍成立。
因此该定理不声称 $X(z_*)$不可计算、不可编码，也不声称一切owner-cooperative增广均不可能。

证明。引理42.1不限制state数据或decoder的数学信息量；它限制的是live executive的实际下一row。
本类没有能独立完成该capture的executive，也没有改变该row的alternate edge。
若通过构造这样的owned接口离开 $\mathcal K$，须另外证明其source／suspension／return关系；
本推论既不提供该构造，也不排除它。$\square$

## 44. 见证自己的记录、账与准确剩余范围

**定义 44.1（实际见证的状态及费用）。** 定理43.1的见证为实际 $H_*$及其真实offer extensions，
不是从另一个成功历史删除输入后得到的同一state。
若 $H_*=z_0\xrightarrow{\kappa_1}\cdots\xrightarrow{\kappa_r}z_*$，则按定义38.1记

$$
C(H_*)=\sum_{j=0}^{r-1}\delta(\kappa_{j+1},z_j),\qquad
P(H_*)=\max_{0\le j\le r}S(z_j),
$$

Native／AA tariffs各用自己的坐标。每个从 $z_*$真正发生的有限offer／forward片段 $\tau$满足

$$
C(H_*;\tau)=C(H_*)+C(\tau,z_*),\qquad
P(H_*;\tau)=\max\{P(H_*),P(\tau,z_*)\}.
$$

所有段在其实际前态计费，不能从另一schedule借bill或从缓冲未消费推论sender免费。
若 $n_N$是该真实prefix的Native原语数，则原receipts／ticks／fees仍是 $n_N,n_N,2n_N$，
Native material仍按定义38.1的 $S_0+b_{control}+8A_{nonmeter}+8n_N$计算。
包括真实support boot、negative polls、spills、copies、描述符／status、发送／接收和已做parent工作；
sender OUT由该sender所属的Native或AA tariff计入。
尚未执行的owed IN没有虚构receipt、tape write或费用；若它已有buffer位，该OUT及backing费用已在账内。
AA实际allocation／grant／reference-bit／field／navigation／I-O／ACK／control及共享ancestor append全保留；
AA22.1的root逐项 $V=1+P+2S$、$S$ headers及 $D$ routing appends仍只是located subcounts。

raw joint endpoint保留定义41.1的所有partial fields，不要求一个tree／available bank／Ready／full token mask。
尤其区分pre-IN与post-IN／pre-WR：后者的真实位已在occupied latch，owed action是WR，不能被写成缺输入。
partial loans、unfinished AA append、status0对象、INPUT／STACK两界、先前capture body、
outboxes／F7／holders／M／ACK／Done／receipt／saved continuations、实际code／control／tokens和meter均按其实际阶段保留。
对parent尚未写出的Done或complete receipt不制造记录，也不从原terminal成功推论它们已存在。
peak沿该同一history计算，按定义38.4包含全部同时retained材料；清scratch不退constructed capacity。
这些是见证的完整账目接口，不是已执行例、完成capture费用数值、统一time界或资源优势。

**定义 44.2（来源与复用边界）。** 本节至第44节所用primitive／channel／partial-state合同统一钉在
`bbf699605ef7faf9f44d3251ef81f246daf4a5a6`，与本卷第26–40节各自引用的原结果按所声明接口衔接。

| 原文定位 | 在本结论中承担的关系 |
| --- | --- |
| [TMC PR57.D1、(PR57.03)、PR57.L1](https://github.com/the-omega-institute/trureturing/blob/bbf699605ef7faf9f44d3251ef81f246daf4a5a6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#L18069) | current literal row、ingress-specific IN、固定successor、逐primitive meter及未完成过程的规定next action；不添加interrupt／wait-any |
| 本卷假设26.2、定义27.2、31.1、34.3、37.3、38.1／38.4 | sender可先OUT；真实空满／latch／backing；IN后WR与status0；ACK全接收；full joint state及same-run bill |
| [LJA4.1](https://github.com/the-omega-institute/trureturing/blob/bbf699605ef7faf9f44d3251ef81f246daf4a5a6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LITERAL_JOURNAL_ADAPTER.md#L243) | busy service仅其规定next primitive；原source token／row seal／delivery ACK与capture入口分开 |
| [AA20.1–20.3](https://github.com/the-omega-institute/trureturing/blob/bbf699605ef7faf9f44d3251ef81f246daf4a5a6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#L1418)及本卷29.2 | 实际root／grants、pending latch、Reserve／edit／Maintain内无新input／query、真实祖先tapes；returned stationary field-read不自动成为busy-owner capture |
| [IR25.2–25.3](https://github.com/the-omega-institute/trureturing/blob/bbf699605ef7faf9f44d3251ef81f246daf4a5a6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMMUTABLE_INTERVAL_REGISTERS.md#L1790) | $J_{\rm IC102}$只在自己的hooked occurrences／owed rows和source mapping上给current capture；新增annex内部仍缺current reentry |
| [RCA15.3](https://github.com/the-omega-institute/trureturing/blob/bbf699605ef7faf9f44d3251ef81f246daf4a5a6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md#L2281) | 同一late-installed graph的canonical-frame历史cut，经finite completion后有later Cover／immutable取得／exact historical Call；不是当前pending action之前的admission |

新增数学内容是引理42.1对buffer空满均成立的owed-row不变量，以及定理43.1对整个
$\mathcal K$、从各自真实successful parent前缀得到的depth-two排除。
没有重证原family、四image inverses、bank transport、AA lifecycle或historical replay，
没有把source-interface census或四个codec名称当作新结果。
文献归属为repo-derived的普通source-model推导；未作外部文献穷尽核查，不主张全球原创性。
这不是新Lean／exact-S或axiom-closure核验、已执行graph或physical conformance证据。

**定义 44.3（未缩减的全目标及剩余义务）。** 第36.4节的全部ordinary mode01 family完成、
第37.1节的准确mode10及原Stop／INITIAL消费者仍各按原条件保留。
本障碍只排除定义41.2的机制类，不交付正面的all-cut capture，
也不以“只捕获poll行”“先完成parent ACK”“只在Entry请求”替代定义41.1。
一般合法增广仍须为全部声明的family／capture interiors及每个有限nesting供应真实admission，
保留Native／AA current authority和全部partial state，取得同一actual prefix的四个独立表达，
以选中received body供应同一个pending consumer的exact continuation及原返回，并给同run记录与费用。
独立receiver／executive、multiplexing或availability路线是否能满足这些条件仍须构造与证明。

IR的declared compiler-cut current结果与RCA的finite-completion-conditional historical closure保持原source区分；
后者已经供应的handler历史closure不被重列为空缺。
定义40.3保留的GENERAL15.5／18.4、RG13.3原Q结果不被缩回单entry；
其外的changed／new rows、broader mixed interiors及full terminal-task kernel仍未解决。
任意internally generated independently guarded policies、all-seven direct schedules、非canonical／physical sources、
实际无限运行、统一有限hardware／resources、total-resource advantage及global／Pareto最小性均未由本结果给出。
最简关系结构及space／time／boundary／memory的实际互恢复全目标保持原范围，未完成。

## 追加锚（本行以下为增补区）

## 45. 现有 J-FAMILY 客户端的当前可见域

**定义 45.1（同一实际启动与精确目标）。** 固定第26–40节的原始安装
`J-FAMILY-ARENA-1`，采用假设26.2、1.2及 AA20.1 的逐点有限材料、工作空间、完整输入及规定确认条件。
所有所需 source／record／port／connection 权限当前独占有效，没有竞争写者、撤权、崩溃或中断。
取定义26.1允许的 $N=0$ 日程：同一次实际 boot、Native 准备 $\xi$、Init及其原返回之后，
真正供应 finish，并执行原 Park／Handback／Stop／INITIAL consumer／ACK／global halt。
四个实际根 $O,F,N^*,r_0$、先行 $O$ 七事件、Native seed／code／prior／saved client及全部保留材料均存在；
未使用的分支也不从该执行或账目中删除。第36.4节供应这条有限完成执行，而非另给一个理想 endpoint。

对该执行的每个有限前缀 $H$，记 $z(H)$ 为其实际出口，$X(H)$ 为定义41.1要求的完整目标：
完整实际有限历史、raw joint endpoint、当前权限、保留材料和实际费用。
其中包括全部 Native PC／code／heads／latches／source16／partial STORE、AA parents／children／headers／tapes、
reserved objects、unfinished append及其真实引用／cursor／subphase／next action，
各连接的真实 endpoint／空满／当前位／backing／pending sender与receiver，以及已发生的 records／receipts。
未完成对象不补入未来字段。$X(H)$ 尤其保留 $h.\mathrm{tail}$ 的真实引用值，
不只保留逻辑树或从 head 可达的词；也不按同构、相同 body或同样终端答案认同来源。

这里的 existing J-FAMILY 没有被赋予 EnableCapture 或 current handler。
定义41.1是另一个实际构造 support、owner、slot、bank后才 enable 的安装所须满足的规格；
若 enable 先于 Init，其覆盖域包含下述原 Init interiors。
本节首先检验现有安装的客户端接口，不把未来 support 当作已安装设施。

**定义 45.2（观察者、记录及保持条件）。** 观察者是现有 serial service client，具有其实际当前 grants、
已经取得或返回的真实 identity／binding，以及现有 request／reply／End／local ACK／Return 连接。
其观察记录 $\mathcal O(H)$ 包含这些连接已经公开的完整 traffic和当前可访问状态，
连同每个已经公开的 Native primitive label、Native row／routine phase／PC、tick及fee pulse、
receipt、stored fence／counter／version、已经取得的 readout及当前合法的付费 closed-cut readout。
保留现有接口中所有这些读数；不删除可区分的旧 stamp，不把 readout 变成免费的当前 snapshot。

观察者的当前 grants不改变 AA20.2及定义29.2的调用阶段。
owner 的额外字段读取仅在自己的 driver已返回、stationary且权限有效时合法；
保留某个引用不自动给出忙碌期间的独立字段调用。
此客户端不是 active AA executor，不另有 administrative socket、外部全 actor scheduler记录、
当前 AA PC、累计 AA field-work invoice、raw allocation probe或独立 serial clock。
AA17.1的签名及 AA20.2的 reply grammar不供应这些额外观察。
$X(H)$、全局 primitive序号和完整成本向量是待恢复目标，不作为观察者已有输入。

在 cut $H$ 上的一个观察实验是该客户端依据已有观察选择动作的有限离散过程。
允许其执行当前合法的 client-local work、已有授权的 Native 观察、真正合法的连接动作和付费旧 cut读数，
但必须保持该 cut自己的原 AA next action尚未执行，不能推进该 active driver以换取较晚 service entry。
这是定义41.1的 pending-consumer条件：观察对象是实验开始时的原前缀，
实验自己的新工作、records与费用仍在各自实际后继中另计。
在两个实验间比较同一确定性 client、相同本地输入和公开选择。
若另用随机输入，只在显式固定同一 random tape时作以下逐步比较；不加入 wall-clock、
scheduler timing、interrupt或其它未声明 side channel。

## 46. 原 Init 中第一条非根增长的真实 tail 切口

**命题 46.1（同一完成执行上的相邻前缀）。** 在定义45.1的一个有限完成执行中，
有两个相邻实际前缀 $H_-$、$H_+=H_-;e$，其中

$$
e=\operatorname{write}(h.\mathrm{tail},c),
$$

是 $r_0$ 上 Init 的首次 $P_R$ 调用在 Maintain 中的真实 AA 字段赋值。
两 cut均已通过该调用的实际 source guard及 source edit，尚未完成该调用的 reply／End／ACK／Return。
其字段与阶段满足：

| 实际坐标 | $H_-$ 的出口 | $H_+$ 的出口 |
| --- | --- | --- |
| $r_0$ 的逻辑 body | $\langle\beta,\beta\rangle$ | $\langle\beta,\beta\rangle$ |
| $h.\mathrm{head}$ | 实际引用 $c$ | 同一实际引用 $c$ |
| $h.\mathrm{tail}$ | null | 实际引用 $c$ |
| $c.\mathrm{side}$、$c.\mathrm{next}$ | $R$、null | $R$、null |
| AA pending control | 尚欠这一次 tail write | 这一次 write的真实 successor subphase／next action |

真实 roots、parents、header及cell bindings与当前 grants在 $e$ 前已取得；$e$ 不重新分配或授权，
不重绑根，不改变 source edge，不发送或接收任何位，也不执行确认。
两个出口均为 raw Maintain cut，不被当作 Ready或一个已返回调用。

证明。定义27.1先在 $O$ 完成七事件及全回复／维护／返回；$r_0$ 此时仍为其独立实际 alpha根。
定义28.1–28.2从本次 Native 原准备、四次完整 Lift及真正 Init取得目标字

$$
E(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle.
$$

在这个 $r_0$ 先完整调用 $P_\varepsilon$，实际 Return，再完整调用 $S_\varepsilon$及 Return。
于是 $r_0$ 的 body为 $\langle\beta,\alpha\rangle$。
owner在 stationary Ready按定义28.2读真实 right field取得 alpha-born $r_1$及其 $R$ 地址／creation关联，
并由 left field取得继续 beta reserve及路径 $L$。
$S_\varepsilon$ 在 $r_0$ 绑定了实际空 header $h$。
这两次编辑都在逻辑根，没有 proper logical ancestor，故没有向 $h$ 追加任何 side。
先行 $O$ 历史的 $P_R$ 不是这里 $r_0$ 的调用，也不向这个 $h$ 写字。

Init接着以定义29.2的 Build消费实收 $E(\beta)$，全局 target为 $R$、birth为 alpha。
该目标是 branch，故 Build先在当前 cone $p_1=R$ 上完整执行相对调用 $\operatorname{Do}(P,\varepsilon)$，即全局 $P_{p_1\varepsilon}=P_R$，然后才可能执行 S及子树构造。
原 Navigate／Guard实际到达 alpha-born $r_1$，其 promotion合法；source template完成后，
$r_0$ 已为 $\langle\beta,\beta\rangle$。
这次 $P_R$ 唯一的 proper logical ancestor是 $r_0$，所以它正是 $h$ 的第一次 append，side为 $R$。

AA20.2的 Reserve先供应所需 fresh source／header／tape material；
Maintain使用其中实际 reserved／allocated cell $c$，初始化 $c.\mathrm{side}=R$、$c.\mathrm{next}=\mathrm{null}$，
再因 $h$ 原为空而写 $h.\mathrm{head}=c$，最后才写 $h.\mathrm{tail}=c$。
这正是 AA22.1的 literal append顺序；Maintain不被另称为分配阶段。
AA20.2明确保留 unfinished append的 references／subphases，故 head已连而tail尚空是原过程的一个 cut。
头可达词已为单字 $R$，但 tail／control尚未完成。
这一 transient distinction及 head-word忽略 tail的投影，直接复用
[Sparse Native Entry Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_NATIVE_ENTRY_ACQUISITION.md)
定义14.1–14.2、23.2，不另立新的 unfinished-tail恢复结论。

假设26.2及 AA20.3、引理28.4、第36.4节给这条 Init及后续 $N=0$ finish的有限完成。
在其中截取 tail write前后的两个前缀即得 $H_-$、$H_+$。
没有删去、交换、重放或改名任何事件，没有从别根或另一次准备借取 cell／grant／后缀。
$H_-$ 欠的是 $e$ 本身，$H_+$ 欠的是原控制图在 $e$ 后的真实下一动作；
不为它们猜定数字行号，也不把二者合并成共同 Ready。
$B_0$ 封存、InitACK、initial carrier及首次 Entry此时尚未来到，不填入其未来值。$\square$

## 47. 完整 Native stamp 下仍相同的客户端记录

**定理 47.1（现有接口上的精确目标不因子化）。** 在定义45.1–45.2的来源、权限、完成及观察条件下，
命题46.1的两个 attained cuts满足

$$
\mathcal O(H_-)=\mathcal O(H_+),\qquad X(H_-)\ne X(H_+).
$$

从二者启动相同确定性 client并保持各自原 AA owed action时，
每个有限合法观察实验的 transcript及输出亦相同。
因此仅由这一接口取得的观察及其后处理，不能在这两个原 cut均恢复精确 $X$；
尤其不能在定义41.1的全部所需 cuts上提供四个各自独立恢复 $X$ 的 space／time／boundary／memory body。
此结论针对 existing serial service-client的观察 map，不对任意合法增广作不可能断言。

证明。$H_+$ 比 $H_-$ 恰多一次 AA 数据字段赋值 $e$。
AA与Native是定义1.4、38.1中的不同 primitive系统，$e$ 不是 Native core occurrence。
故 Native tapes／heads／latches／PC、完整公开 Native labels、receipts／ticks／fee pulses，
全部既有 fence／counter版本及已取得 closed-cut readout在两侧相同。
TMC PR57.D1、D3及L2的公开 PC／meter是 Native row／occurrence的观察；
不能把其中的“每次 occurrence”改成“每个 AA或Native动作”而添出一个全局钟。
从相同实际 Native tapes／fences开始的合法付费旧 cut readout也读到相同数据，
其自身后来产生的 Native receipts／费用照常计入两侧实验。

$e$ 没有 request／reply bit、End、local ACK或Return输出。
两侧先前的 AA traffic、已公开 reference／descriptor／creation关联及当前客户端可访问连接状态相同。
这包括任何已由真实 sender供应的当前 input bit、occupied latch、backing及pending endpoints；
它们在两个前缀间按同一实际对象保持，不能由“Maintain不接收新query”推出“所有连接为空”。
$P_R$ 的源编辑已经发生，但其后 BuildAnswer／Print／End仍未执行，
不把一份将来的 Growth回复预先加入任一观察记录。

两 cut都在同一 active $r_0$ driver的 Maintain内。
AA20.2在 Reserve／editing／Maintain不 admit新 input或query；
定义29.2的 extra owner field-read须待driver返回且stationary。
因此保留引用与grant均不供应一个当前 $h.\mathrm{tail}$ 读取，
也不能在此另开 Tag／FetchGrowth／Next或把一个错阶段调用当作 emitted Busy reply。
定义37.2的 busy／missing-right disabled none、真正执行的 source refusal、BadFrame及OutOfRange仍分开。
原图的两个不同 AA next rows属于 $X$，不是客户端可读的 AA PC或 availability port。

现在对实验长度归纳。起点的整个客户端可见记录、client-local state、
其可访问的 Native数据、tokens／grants与连接位均相同。
若前 $k$ 步的观察相同，同一确定性 client选择同一下一动作。
client-local计算及已有授权的 Native读取只依赖相同可访问数据；
连接操作按相同实际 endpoints／空满／当前位／backing前置执行，
其余合法 Native工作与旧 cut readout也由同一前态给出相同 effects、public labels及返回值。
故这些动作的合法性和第 $k+1$ 步观察均相同。
任何首次推进 active $r_0$ driver的尝试，首先须执行该 cut自己的 owed action，
而这被实验保持条件排除；等driver完成后的owner读取亦不是这个 cut的观察。
阶段禁用本身不是新增回复。这样归纳得到每个有限 transcript相同，
观察决定的停机与输出也相同。若使用随机输入，固定同一 tape后论证逐条成立；
这里不据此宣称任何额外 timing或scheduler可观测性的等价。

另一方面，$h.\mathrm{tail}$ 在 $X(H_-)$ 中为 null，在 $X(H_+)$ 中为同一实际非null引用 $c$；
实际历史、AA pending control及已发生AA field-work也不同。
故 $X(H_-)\ne X(H_+)$ 不依赖 fresh-name拼写、逻辑树差别或终端答案差别。
若某方法只由上述记录构造 body并由该 body恢复 $X$，
两侧相同记录及相同本地选择给相同 body，decoder遂给相同结果，不能同时等于这两个不同 $X$。
这是已有的观察纤维／factorization原则在此 attained pair上的直接应用，非另一个通用新定理。
对四个 body中的每一个分别如此；联合取四个旧接口后处理也不会切开该纤维。$\square$

**定义 47.2（该相邻事件的完整账与权限）。** 沿定义38.1、44.1的同次实际前态计费，记

$$
\begin{aligned}
C(H_+)&=C(H_-)+\delta(e,z(H_-)),\\
P(H_+)&=\max\{P(H_-),S(z(H_+))\}.
\end{aligned}
$$

$e$ 的 located AA data-field-assignment次数恰增加一；
其真实 reference-representation及其它实际 tariff坐标保留在 $\delta$ 中。
Native occurrence／receipt／tick／fee的增量均为零。
这不是“整个账单只加一”，也不是两个实际成本向量相等。
AA事件本身、所有已经产生的AA records／receipts与不同的field-work费用都在 $X$ 中，
不能因为客户端未取得它们便抹去。
定理47.1只说该 installed client没有由会计坐标自动获得一个当前可调用 live AA invoice；
账目存在和它的当前取得是不同关系。

所有 $O,F,N^*,r_0$、其source vertices／parents／headers／tapes、Native准备、mandatory backing、
当前连接／latches、reserved material／pending cursors和其它定义38.4材料继续按真实 prefix保留。
同一cell及root binding不是重新取得的复制品；current exclusive grants没有跨 $e$ 改变。
没有remote dereference、root rebind、loan、rollback或restore来供应这两个cut。
peak沿该同一history取同时retained材料最大值，不从“无新allocation”推断所有reference位或peak费用不变，
也不把后续清理解释为退还constructed capacity。
这些式子给出精确向量关系；不赋予一个未规定的数值总tariff、物理价格或资源优势。

## 48. 来源对应、可区分义务及未决范围

**定义 48.1（所复用的来源与新增对应）。** 第45–48节所引原文固定于
`1db40b9b076fbd5d454746cc1be7fce51ebec594`；第26–44节已有的各自来源合同按原域使用。

| 原文定位 | 在定理47.1中的用途 |
| --- | --- |
| 本卷假设26.2、定义27.1–27.3、28.1–28.3、29.2及引理28.4、定理36.4 | 四个真实根和先行历史、实际Native准备／Init、首个alpha-born cone上的 $P_R$ 以及 $N=0$ 的真实完成后缀 |
| [AA17.1、20.1–20.3、22.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | 实际引用／当前权限、无独立serial clock的签名、Reserve与Maintain、link-before-tail顺序、phase disabling及有限返回 |
| [AA21.1、22.3](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | semantic service与完整controller chronology分离；会计和额外可访问side information的条件边界 |
| [Sparse Native Entry Acquisition14.1–14.2、23.1–23.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_NATIVE_ENTRY_ACQUISITION.md) | 已有unfinished-tail／content-vs-control区别；owner-local付费evaluator属于其另有权限及调度的安装，不供应本client的busy读口 |
| [TMC PR57.D1、D3及L2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)及本卷38.1 | 公开Native row／primitive trace、receipt／tick／fee及付费closed-cut读数；AA／Native分坐标 |
| 本卷37.2–37.3、38.4、41.1、44.1 | 原标签、full raw target、保留材料、每个cut自己的owed action及完整实际费用 |

unfinished-tail区别、AA literal append、完成性和观察纤维原则均为复用。
这里的具体对应是：原 J-FAMILY Init真正到达 first-$P_R$ 的相邻tail赋值cut，
其完整现有 Native public stamps及客户端traffic保持相同，而完整raw目标与AA账不同。
文献归属为 repo-derived 的条件性普通source-model推导；未作外部文献穷尽或repository-wide新意认证，
不主张新的通用indistinguishability原理或全球原创性。
本对应没有新Lean／exact-S编译或axiom-closure核验，也不提供运行时执行见证、physical conformance或whole-run数值测量。

**定义 48.2（后继安装上的适用条件与必要区分）。** 若后继安装要把本见证用于自己的current取得规格，
须先证明它自己的真实boot／rights／事件到原 $H_-$、$H_+$ 的source-prefix对应，
且在保留各自原pending action时，所比较观察map仍把这两个对应前缀置于同一纤维。
新support、logger、meter、scheduler或owner角色的发生及其观察不能被此对应静默删去。
仅body相等、端口同名、同一计数或可编码性不构成这个桥。

在这种对应确已成立的安装上，若欲精确恢复保留的raw目标，
就必须由当前合法且真实付费的观察切开这两个不同目标；否则定理47.1的等记录论证仍适用。
一个真正取得的 current AA field-work count会在此pair上相差一，
current AA row、$h.\mathrm{tail}$ 或包含该AA步的真实all-actor trace也能区分它们。
这说明额外观察会改变纤维，不断言上述facility已经安装，不规定必须采用哪一种机制。
只取得一个区分bit至多破除此pair，不能由此推出完整历史／raw state的充分恢复，
更不能推出授权、snapshot／restore、原continuation或quantum-event facility。

**定义 48.3（保持原量词的边界）。** 定理47.1给现有接口的一条visibility必要条件，
与定理43.1对 $\mathcal K$ 的admission障碍承担不同关系。
不从这两条局部结论推出所有outside-$\mathcal K$增广不可能，
也不把第36.4节的完整ordinary family、准确mode10或原Stop／INITIAL完成缩成只有 $N=0$。
$N=0$ 只供应该全域中一个真实反例路径；原完整输入域及其所有cuts仍按定义41.1保留。

完整的正面current构造仍须在自己的原来源上供应真实Native／AA admission、
当前owner-bound suspension／disclosure、任意有限重复与任意有限深度nested requests，
包括新增handler interiors，保留全部partial states、rights、records和实际费用；
四个独立取得且各有source解释的完整表达须恢复同一actual prefix，
由实际选中的received body接回该cut自己的同一个owed action并恰执行一次，
缺输入时仍等待它自己的输入，再忠实接回全部原返回及terminal消费者。
现有serial接口的非因子化不供应其中任何capture／return实现。

定义40.3、44.3保留的既有结果继续按各自来源和域成立：
RCA15.3的finite-completion-conditional历史handler closure不重列为未解；
IR的declared compiler-cut current结果不自动覆盖本AA安装；
GENERAL15.5／18.4、RG13.3的既有cross-entry／inherited original-Q域不缩回单entry。
其外的changed／new rows、broader mixed interiors及full terminal-task kernel，
更广内部守卫策略／all-seven direct schedules、generic或physical sources、
实际无限运行、统一有限hardware／resources、total-resource advantage和global／Pareto最小性仍未由此给出。
空间、时间、边界、记忆的最简关系结构及实际互恢复全目标保持原范围。

## 追加锚（本行以下为增补区）


## 49. 同一来源上的局部日志与保留活动

**定义 49.1（条件增广的载体）。** 记第26–40节的一次实际 J-FAMILY 组件为 $J$。
本节至第52节及[同主题续卷](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION_II.md)第53–59节定义其条件增广 $J^+$。
它从这个组件自己的不可约入口启动，保留唯一实际准备 $\xi$、原 beta seed、原 Native 细胞、代码、PC、heads、latches及tokens，
保留四个互异的实际 AA 根 $O,F,N^*,r_0$、固定根槽、驱动器、supervisor、真实 parent及共同祖先 tapes。
增广绑定这些实际对象，不另选一个相同 body 的源，不把 AA 初始 alpha 当作 Native 初始 beta。
新的类型、分配域、工作区、日志和协议连接与原对象分开；原根槽与原源连接不重绑定。

原端口及所有者仍为第27.1节的0–77，工作池仍恰为1–12，16／17／25／27／74仍受原保护。
原48–51路线、四个固定 AA request／reply／End／local ACK／same-root Return连接束，
以及第27.2节五条外层连接的实际 sender、receiver、queue、latch、backing和控制器均属于载体。
动态出生的源顶点、header、tape、reserved object及尚未链接的记录以实际分配返回绑定加入载体。
支持过程使用自己的材料及授权，不借用部分转交中的原十二字工作池。

**定义 49.2（原始状态与切口目标）。** 一个 raw 状态 $z$ 是有限有类型对象映射及其实际关系：
字段可为未初始化、null、有限符号、比特或实际引用；各状态互不混同。
映射包括分配后未链接对象、status0、部分长度／body／ending、原 source16／partial STORE、
AA未完成 Reserve／source template／Maintain、全部真实根／parent／child／header／tape、
有限控制及引用寄存器、实际细胞和mark、每条连接的当前位及空满、已收未back的latch、发送者及接收者阶段，
以及已发生的原记录和支持记录。权限为独立的当前关系 $\mathsf{Rights}(z)$，对象中描述的权限字不构成该关系。

从实际入口至一个有限原语边界的历史写为 $H$，出口为 $z_H$，定义

$$
X(H)=\bigl(H,z_H,\mathsf{Rights}(z_H),C(H),\mathsf{Ret}(z_H)\bigr).
\tag{AS49.1}
$$

$H$ 包括真实输入来源、实际返回引用、同值写入、拒绝、原meter coeffect及所有支持动作；
$C$ 是第58节定义的实际前态费用向量，$\mathsf{Ret}$ 是同时保留的实际材料。
目标不对引用重命名、不只取逻辑树，也不把两个终端答案相同的历史认同。
未初始化字段保持未初始化，未发生的seal、Done、完整receipt或未来输入没有值。
原 parser 的冻结 INPUT 界与自己增长的 STACK 界分别在状态中保存。

**定义 49.3（活动、保存范围与公共增长）。** 实际选择字段 $\mathsf{Active}$ 的值为永久基本活动 $b$ 或一个支持活动 capsule。
基本活动指向定义49.1的全部原组件及其参与者。
一个 capsule $c$ 恰有固定字段

$$
(\mathsf{parent},\mathsf{cut},\mathsf{peer},\mathsf{key},\mathsf{localRoot},
\mathsf{pc},r_1,r_2,r_3,r_4,\ell_1,\ldots,\ell_8).
\tag{AS49.2}
$$

前五项及四个 $r_i$ 是实际引用或null，PC取固定有限程序中的标签，八个 $\ell_i$ 是有限符号latch。
任意长计数、路径、解析栈、遍历栈、缓冲、环境和连接状态均是实际构造的记录，
由 $\mathsf{localRoot}$ 或上述寄存器取得；原语之间没有另存于解释器外的隐含寄存器或宿主栈。
一个额外的有限字段机引擎解释被选capsule。同一个引擎可解释任意多实际出生的capsules；
动态活动数是数据量，不是引擎数或深度编号的代码数。

每个原mutator及原通道参与者的组为 $b$，支持对象及其协议peer的组为其实际capsule。
动态对象继承创建规则规定的实际组绑定。
活动 $p$ 的操作框架 $\mathsf{OpFrame}(p)$ 包括其原有运行堆、控制、heads／latches、
寄存器、pending action、私有工作及被保留的连接状态和原权限。
公共日志尾、追加分配inventory、累计账、子活动档案、进入／退休元数据不属于此框架。
它们仍属于 $X$，并在子活动执行时继续增长。
因此“保持父活动”表示父操作框架及其所欠动作保持，不表示整个世界或全部费用回到旧值。

**定义 49.4（声明的完整输入与请求域）。** 一次安装先于全部未来输入。
ordinary域仍是第26.1节的每个有限 $N\ge0$、实际adaptive的
$A_i\in\{\mathsf{Rho},\mathsf{Left}(v_i),\mathsf{Right}(v_i)\}$、
在原raw ingress真正取得的任意非空有限有序树 $v_i$、分别在原GuardIngress收到的有限
$1=g_0\le\cdots\le g_N$，以及实际finish。
$t_0=\beta$，$\varepsilon_i=[n(c_{A_i}(t_{i-1}))\le g_i]$，
$t_i$ 按第26.1节取候选或原值，不能从捕获请求预知下一普通输入。
mode10恰保留第26.3、37.1节：C0 guard2，C1 guard2或guard4，
C1全结算／AfterFinal／Entry／Select之后才接收C2；拒绝C1时C2为Right(alpha)、guard至少2，
接受C1时C2为Rho、guard至少4。mode00、11保留原raw／局部退出边。

在实际付费 EnableCapture 完成后、吸收global halt之前，每个真正到达的原或新增原语边界均可请求。
包括 Init、部分十二TOK、arena／Build／rho／navigation／ancestor维护、candidate、F7／holder／association、
Input22、variable-depth decoder、forest、settlement／receipt、Park、terminal ACK，
以及下文安装后支持程序的分配、接收、解释、复制、检查、部分回写与返回内部。
请求可有限重复并形成任意有限有序嵌套森林；不预先限制树高。
每个请求的目标前缀是首次capture side effect之前的实际前缀，
不能先执行该cut的owed action或等待原过程完成以取得入口。
已使能且已有genuine buffered bit的IN也在域内；缺原输入的动作返回后仍缺它自己的输入。

## 50. F0–F4的有限足迹、当前授权与原子边

**假设 50.1（F0：真实入口及有价安装）。** 在首个原boot occurrence之前，供应一个有限primitive recorder／gate入口及真实genesis。
genesis只含原不可约Native入口及有限支持控制／endpoint根的实际绑定与规定常量，
不含未知seed、代码、输入或既存未记录历史的免费snapshot。
未知字由其原有后续IN／WR及构造操作进入。日志从这个入口起记录支持安装和原boot。

原所有者实际委托三个相互有别的当前行政能力：源绑定的invocation gating、
各局部规则实际effect disclosure、held-context控制字段访问。
这些不是旧AA源grant、一个descriptor或OC的ReadPC能力的推论。
以逐比特／逐字段操作构造有限literal支持代码、类型、根槽、banks、连接backing和grant表示，
执行实际原bootstrap、四根初始化、$O$七事件、原Native准备／seed／saved client。
支持code／banks／所需source bindings完成后，才付费写 EnableCapture，且在首个覆盖runtime过程之前。
本假设供应有限primitive基础及其材料，不声称由旧动作菜单或从无硬件构造此基础。

**假设 50.2（F1：真实有限effect日志）。** 固定原与新增primitive规则的有限schema并集。
每个core occurrence $e$ 有固定有限足迹；instrumentation由相应owner当前授权，
披露这个occurrence的实际读数／结果、改变的位置和值、真输入／输出origin、有限控制后继、
权限变化及新返回对象绑定。Native EX须另把真实新细胞绑定到custodian endpoint；
这是新增coeffect／grant，不是将整数位置cast成地址。

覆盖schema为Native RD／WR／ML／MR／EX／BF／IN／OUT／TOK／CTL及原meter coeffect，
AA一对象分配／授权、null与引用测试、个别字段、bit I/O、ACK及control，
所有建模的sender／receiver／queue／backing动作，以及全部支持规则。
大字运算、复制、可变深度解析与导航均展开为这些规则序列，不作为一个payload。
存在由这个有限schema并集决定的常数 $B$，每条core记录至多有 $B$ 个位置／值／绑定项。
一个值项是比特、有限符号、字段标识或实际引用；任意长word不成为一个值项。
引用在本理想模型中是原子的有类型绑定，其实际表示宽度及访问费用仍逐项承担，未假设固定bit宽。

设 $L$ 为实际不可变event journal尾。一次联合occurrence先执行core，
再以一个固定schema的有界coeffect取得真实fresh节点 $j$，写 $j.\mathsf{prev}=L_{\rm old}$、
core tag及effect tuple，并把 $L$ 置为 $j$。
节点自身的birth、字段、read／retention grants、inventory登记与tail写入由这一固定规则决定，
从真实 $j$ 绑定和payload恢复；不把这些动作再调用成另一层logger。
节点schema、inventory entry及登记写入的字段数均有固定界。
coeffect与core同属一个原子occurrence，正如原Native receipt coeffect；
软件读取、序列化、输出这些节点则是普通可被嵌套的工作。

custodian独占日志写权，持每个真实闭合prefix的read／retention权。
每次core分配和coeffect birth都把真实typed binding及合法endpoint登记到保留inventory；
该追加inventory不只登记从完成root可达的对象，因而包括reserved、unlinked及未初始化对象。
当前inventory尾可增长，旧entry／旧闭合区间不可变且可按原绑定访问。
每次occurrence供应其实际有限node、字段及reference backing；
本条把该有限足迹coeffect声明为原子基础，不声称已有逐bit实现。

**假设 50.3（F2：全参与者门控与有限进入）。** 除下述独立授权ENTER边外，
每个能改变定义49.2状态的参与者，在每次调用时都检查自己的实际组等于 $\mathsf{Active}$。
这包括原sender、queue、receiver、backing控制器及动态出生参与者，不能只停接收executive。
没有未建模DMA／kernel／queue写入、竞争写者、撤权或崩溃。
门控比较用实际绑定相等，其表示访问计费；recorder是联合规则的coeffect，不是另一个可被调度的mutator。

在enabled且prehalt时，$\mathsf{ENTER}(\mathit{peer},1)$ 要求当前合法wake权限、
实际授权peer的一次genuine one-bit handoff及足够fresh材料。
此handoff含该sender自己的实际有限控制effect；它不消费任何原request、parent ACK或原input连接。
此前任何已经发生的发送／backing仍属于进入前缀。
设调用前 $\mathsf{Active}=p$、$L=l$。该边原子地出生capsule $c$ 和key $k$，写

$$
\begin{gathered}
c.\mathsf{parent}=p,\quad c.\mathsf{cut}=l,\quad c.\mathsf{peer}=\mathit{peer},
\quad c.\mathsf{key}=k,\quad c.\mathsf{localRoot}=\mathsf{null},\\
c.\mathsf{pc}=\mathsf{Entry},\quad r_1=\cdots=r_4=\mathsf{null},
\quad\ell_1=\cdots=\ell_8=0,\\
k.\mathsf{child}=c,\quad k.\mathsf{parent}=p,\quad k.\mathsf{unspent}=1,
\qquad\mathsf{Active}=c.
\end{gathered}
\tag{AS50.1}
$$

新peer工作归这个capsule组。只有gate custodian可使用ENTER／selector权；
key生命周期字段只有custodian的ENTER／LEAVE可写，普通支持字段写及收到的identity字不能重置它。
该边只创建两个固定schema对象、写一个selector及有限handoff字段，交给F1记录。
它不复制parent heap、PC、latch或任意环境，不推进父动作；父对象留在原处。
这是新固定元数的reference原语，既不是旧CTL，也不是批量save／capture。

每次实际进入供应相应fresh capsule／key材料。
同一个支持引擎及当前peer获得独立于被停row的执行服务，不依赖父pool、父ACK或父过程完成。
不供应每个深度一个新engine，不设固定emergency frame数；实际frame数可以随有限树高增长。
ENTER前后都是覆盖边界，入口没有另一个须先完成的软件save prologue。

**假设 50.4（F3：个别字段、当前绑定及独立交通）。** 支持有付费个别字段read／write／test、
固定schema一对象allocation、有限control和实际构造one-bit channels。
分配返回真实引用、未初始化字段及其实际初始化／读取／扩展grant；初始化仍是个别写。
引用可按AA理想约定复制／比较，承担实际表示费用。
没有原子arithmetic、seek、word-copy、字节到引用转换或完整状态读取原语。

custodian另有源绑定且只对held parent有效的个别运行控制endpoint：
Native的真实PC／latch各有限字段、各实际head-mark细胞，AA及支持的PC／latches／reference registers。
基本活动按实际owner／field的有限schema case访问；动态后代仍从真实birth binding取得endpoint。
支持parent通过它的真实capsule访问。变量栈及环境的heap对象留存，不批量加载回另一个源。
本授权也包括本载体各运行sender／receiver的相应控制字段；
原heap payload、source edge及原port token不从字节反序列化成执行能力。

解码得到的identity word须逐位全比较实际inventory中条目的完整identity，
由匹配entry提供已经存在的typed binding，之后另查当前custodian／owner授权。
不从历史权限描述恢复grant，不以相同body、位置数或名称建立绑定。
对切口 $H$ 已存在的引用，resolver冻结到 $H$ 的实际inventory端点；
这个端点可由 $X(H)$ 的真实记录得到，所需绑定都已在其出生时登记。
后来的child birth或扫描自身日志不扩展这个搜索区间。
当前 $c,k$ 等直接操作数来自真实capsule／custodian绑定，不从旧目标制造未来引用。

每个capsule以自己的fresh allocations／endpoint grants构造channel／backing和完整peer／sender／receiver状态。
四条delivery路线及另一个selected-body／ACK协议路线与原及ancestor连接分开；
每一确认有指定方向、origin和使能阶段，位相等不替代真实ACK。
部分连接构造也是raw状态。每个请求的合法有限framing、分stage traffic与规定genuine ACK、
足够有限workspace及fresh材料均实际供应；active本地动作与peer在有限干扰后进展。
本条不供应缺失的原ordinary input，不让父receiver先消费自己的位来为child腾入口。

**假设 50.5（F4：一次线性释放）。** 新原语 $\mathsf{LEAVE}(k,p)$ 要求custodian实际持有key，
$\mathsf{Active}=k.\mathsf{child}$、$k.\mathsf{unspent}=1$、$p=k.\mathsf{parent}$。
它在同一个原子边写 $k.\mathsf{unspent}=0$、把child标为retired并令 $\mathsf{Active}=p$，随后由F1记录。
只有custodian可调用；参数 $p$ 必须由实收body中的parent identity解析、经真实inventory绑定并与key比较。
软件在完成全部检查及个别控制字段回写后才调用此边。

这一个有限guard不检测整body、heap相等或snapshot正确性，不执行任何owed parent primitive。
它只检验当前top／parent／unspent字段，写spent／retired／selector及有限控制。
所有真实比较、reference表示、写入和journal材料计费。
key消耗与selector转交之间没有软件边界；若把本原语细分，其新增内部边界不由本假设自动证明覆盖。

**定义 50.6（基础的条件层次）。** F0–F4均为 $J^+$ 的新增理想source-model前提。
其中“有限足迹”指固定字段／引用项数，不指固定bit数或一次完整状态动作。
实际委托、当前grant、全mutator接线、足够材料与原子完成均须与这些规则同时成立。
其在未改装J-FAMILY或任意host上的可用性记为 ASSUMED-UNVERIFIED；
支付下文tariff只使成本账完整，不证明这些设施已经存在。
本模型不以Capture／Restore／Ready／Return之名另假定待证的全状态取得或返回结论。

## 51. 固定程序、实际源绑定与冻结扫描

**定义 51.1（安装的先后与有限控制）。** 将原有限代码与支持的下列控制和有限schema作不相交tag联合：
Entry、BuildChannels、ReceiveRequest、Collect$(a)$、Interpret$(a)$、Emit$(a)$、DeliveryACK$(a)$、
ReceiveSelection、ReceiveSelectedBody、Verify、Reinstate、Leave，
其中 $a\in\{\mathsf S,\mathsf T,\mathsf B,\mathsf M\}$ 只有四种固定case。
分配、字段测试、固定分支和循环按TMC PR57.D1／(PR57.03)的有限图展开法解释；
新增reference字段机是F3明确给出的基础，不冒称旧Native仅有固定端口的CTL已能执行它。
数据深度、ordinal、frame长度、对象identity及返回环境均存于已构造记录。
所有实际活变量都在定义49.3的capsule或由它可取得的heap中。

先写literal支持schema／程序表，再写其表外完整description及identity，
再把实际endpoint／source bindings写入并seal；新identity沿用第27.3节的先表后描述、后绑定规则。
$O,F,N^*,r_0$只来自四次真实allocator return，$O$七事件照原先后完整发生；
新cone仍从 $r_0$ 的真正reserve spine产生，保留非null parent及全部共享ancestor append。
记录从boot前开始，因此这些bindings、Native准备及Lift／Init的真实输入不是genesis猜定字。
EnableCapture只在相应安装条件完成之后发生，未来 $N$、operand、guard、请求数及树高均不进入代码表。

**定义 51.2（无嵌套时的一次处理）。** ENTER的前态历史为 $H$，新capsule为 $c$，
故 $c.\mathsf{cut}=L(H)$、$c.\mathsf{parent}=\mathsf{Active}(H)$。
Entry保留这两个真实值，逐字段构造自己的工作root、渠道及peer状态，
收完wake之后的合法有限request frame。每次bit IN先占pending latch，
写完整backing后才清latch并开放下一位；length／body／ending均有独立cursor及未完成状态。

对四个 $a$ 分别执行一次新的Collect：从固定 $c.\mathsf{cut}$ 沿prev读到genesis，
将每个实际node及payload压入新构造栈，再由栈得到正序。
不追逐正在增长的全局 $L$，也不把第一个body或其解码结果作为另三个producer的输入。
各producer有自己的遍历、workspace、framing、完整body、mailbox及requester destination。
Interpret按第52节该表达的实际结构构造字，Emit逐bit完整交付，
目的块在全长度、全body、全ending及backing完成后才seal；再接收属于这次delivery的genuine ACK。
四份交付分别完成，四个requester块互不alias。

requester实际取得四个完整块后作有限choice，发送种类及所选块的整个实收body，
包括长度、每一bit、完整ending和该协议规定的真实ACK阶段；不能只送一个choice index。
ReceiveSelectedBody用新的backing接收，直到完整检查前保持未完成状态。
每个原ACK、delivery ACK、selected-body确认及parent输入保持自己的端点、方向和来源。

Verify全解析实收body的schema、source／install identity、闭合cut binding、
parent identity、表达grammar、长度及完全exhaustion，
并付费逐位全比较该body与相应真实已发出的完整body。
比较给出正确性及出处验证；实际出处首先来自允许的journal读取、写入和复制链，
一个自称origin的字符串不单独认证来源。
支持不是敌意writer／损坏信道的密码协议，完成定理只量化F3规定的合法忠实traffic。
不完整traffic只有其raw前缀，不预先产生成功body或原任务回应。

**定义 51.3（实收值的运行消费）。** Verify成功后只从所选实收body的解码结果
$\widehat X$ 取得held parent的运行context字段及 $\widehat p=\mathsf{Active}(\widehat X)$。
按其对象／字段表逐项列举PC、latches、reference registers及实际head位置。
identity字段通过F3的冻结inventory扫描解析为真实binding，另检查当前行政授权。
随后用这些实收值作为真实held-context写的操作数：写PC／latch字段、写相应引用寄存器，
对每个Native head在实收位置选定的真实细胞上写其mark为1。
保存范围内其它mark和heap留在原处；正确traffic时这些写入逐项幂等，其证明在第55节。
没有从一个隐藏backup加载context的另一条路径；对应已发body只供验证。

最后把从实收identity解析的 $\widehat p$ 交给 $\mathsf{LEAVE}(c.\mathsf{key},\widehat p)$。
重新被选择的原解释器／driver实际读取这些PC／latch／register／head字段决定下一动作；
因而实收数据不只是审计材料，parent参数也不由一个未使用body旁边的旧快照替代。
原源edge、heap payload及token owner均不反序列化，不rollback journal、账、records或constructed capacity。

**定义 51.4（所有循环的有限输入端点）。** 每次Collect冻结旧journal tail。
对frame扫描先固定完整marked length及ending界；对parser保留冻结INPUT集合与独立STACK界；
对identity解析固定切口的inventory端点；对graph／fold遍历先固定所消费节点集及其constructed stack边界。
可以逐字段建立这些有限输入，但每一步的已得端点、余量及未链接对象均保存在raw状态中。
扫描自己的journal coeffects只使公共历史增长，不改变这次扫描的输入端。
需要的parent引用在所捕获cut已出生，故不必搜索未来inventory entries。
暂存栈的push／pop及余量是实际数据操作，不以不断重取全局tail作为循环条件。

当parent本身正在这些步骤中时，新ENTER直接保留其当前capsule和heap，
包括null localRoot、刚分配未链接cell、尚未seal body、占用latch、半写parse frame或下一个回写index。
child不要求parent先完成任何上述操作。第54–56节对同一schema给出统一证明。

## 52. 真实局部记录所确定的四种来源表达

**定义 52.1（闭合日志的fold）。** $L(H)$ 的prev链给出真实联合occurrences
$e_1,\ldots,e_m$，每项携自己的真实journal-node binding。
从真实genesis开始，$\mathsf{Fold}$逐项执行该schema的core effect，
再执行F1的固定节点birth／payload／grant／inventory／tail规则。
这里执行发生在重建数据上，不重放到live source。
有限状态、未初始化标记、实际alias、权限关系、保留材料与每个tariff的实际前态均随fold保留。
$\mathsf{Fold}$的正确性为续卷定理54.1；此定义没有假定old meter已记录private值。

**定义 52.2（各自的完整结构）。** 对同一个实际 $H$，每个body有共同有限头：
真实genesis／安装schema、source及install identity、旧cut实际binding和种类tag，
再接该种结构的完全literal序列化。自然数字用 $U(n)$，有限字用 $B(w)$，
固定tuple用 $T_r$；字段以type及已初始化标记区分null与未初始化。
对象identity按实际绑定表示，真实birth／endpoint关联也在结构中保留，不按body相等合并。
四个主体如下。

时间表达 $\mathsf T(H)$ 是从genesis到旧tail的实际有序联合occurrence序列，
含actor／row、实际读写位置与值、分配／返回绑定、I/O origin、原及新增coeffects。
它的逆按该顺序fold；各费用在重建的真实前态计算。
该表达保留同值写入、source refusal、失败测试及ACK事件，不能只取改变了逻辑树的事件。

空间表达 $\mathsf S(H)$ 是实际object／cell／endpoint与occurrence顶点的有限typed incidence graph。
边标明birth、read、write、grant、root／parent／child／header／tape及channel关联，
字段保留每次版本及未初始化状态；一条特别的occurrence前驱spine保留真实总交错顺序。
同一个引用的alias边相交，不同occurrence的相同子树不合并成一个源。
逆沿这条spine读取关联effect tuple并fold。
这是这个来源的有版本位置关系，不把当前AA逻辑树 alone 宣称为完整历史。

边界表达 $\mathsf B(H)$ 是这些真实primitive boxes的有序复合图。
每盒保留literal row、实际读／写／I/O terminals、真实绑定及前后字段版本；
carry wires携带未改变位置、alias与权限事实，genesis和最后raw boundary均在图中。
逆按保留的盒顺序切开复合，读取完整terminals，恢复同一occurrence序列再fold。
这里的boundary是完整内部event-interface边界，未声称旧外部traffic边界已足够。
图中carry域在有限 $H$ 上有限；生产这些线及terminal数据仍用实际有限扫描和写入。

记忆表达 $\mathsf M(H)$ 是从旧tail可达的真实不可变journal-node heap及genesis，
节点携其真实identity、prev及所有payload字段。
逆逐prev遍历、反转并fold；日志本身的birth／grant／字段／tail也由固定coeffect恢复。
原archives、其它raw状态和support的旧状态由payload解释恢复；
本表达没有抹去未从完成源root可达的reserved material。

**定理 52.3（同cut四表达的逐体逆）。** 在F0–F1的真实记录条件下，
定义52.2每个完整body各自决定 $X(H)$，且它的source meaning就是该同一个 $H$ 的上述实际结构。
具体地，若 $\mathsf{Body}_a(H)$ 为完整序列化，则

$$
\mathsf{Dec}_a(\mathsf{Body}_a(H))=X(H)
\qquad(a\in\{\mathsf S,\mathsf T,\mathsf B,\mathsf M\}).
\tag{AS52.1}
$$

证明。时间body给出全部tuple、顺序及真实node binding。
空间body的特定spine唯一规定顺序，每个incident tuple保留其tag与完整字段；
边界body切回有序boxes后同样给出这些tuple；记忆body的prev链接给同一序列的倒序。
完整framing／type／exhaustion使每一步都没有遗漏或额外字段，重复引用按同一identity解析，
未初始化与null保持不同。因此四条逆均归约为定义52.1的同一个fold。
定理54.1逐occurrence证明该fold确为真实 $X(H)$，从而给(AS52.1)。
这也证明每个body的实际结构含义，不把旧RG image定理按名称移到这个新图。
有限codec、graph序列化及fold是复用方法；此定理关于它们在所给真实局部记录上的对应。
有价的四份独立生产、实收消费和当前返回另由续卷第53–57节证明。$\square$

**定义 52.4（表达转换与实际操作的区别）。** 在上述实际image上，
$\mathsf{Enc}_d\mathsf{Dec}_a(\mathsf{Body}_a(H))$ 是同一目标的 $d$ 表达。
这给数学互恢复，不赋予当前位置的grant、独立producer或return能力。
定义51.2的四次真实遍历和完整交付供应各自实际取得，定义51.3及第55节供应运行消费。
“独立”指每个received body单独可逆且分别生产／交付，不指统计独立、最短表示或新增四个独立源。
实际body字、解析／比较、inventory扫描及所有转换均按其实际动作另计费。

## 追加锚（本行以下为增补区）
