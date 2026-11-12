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
