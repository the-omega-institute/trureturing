## 53. 全有限请求森林的条件当前供应定理

**定义 53.1（续卷的对象与证据范围）。** 本卷接续
[原子供应替换](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION.md)第49–52节，
其中的 $J^+$、$X(H)$、capsule、F0–F4、固定程序及四表达在这里保持同一定义。
下文AS指该卷，AA指
[Atomic Generation Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)，
TMC指[Transport Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)。
这里给普通条件数学构造与证明；新组合没有Lean kernel、运行时执行或物理符合性证明。

一个有限请求森林是有限多个有序root请求及其有限有序child请求树。
child在其parent处理的一个真正到达原语边界进入，返回的consumer是那个partial parent的所欠动作。
root在原活动的真正到达边界进入。每个请求均有F3的实际合法有限traffic／ACK／材料；
森林只规定实际有限请求，不为一个无限请求流承诺终止，也不把树高作为安装参数。

**定理 53.2（局部日志与保留活动的当前供应）。** 假定AS50.1–50.5全部成立：
真实记录从该组件自己的不可约boot入口开始，当前owner实际委托所有披露、门控、held-context权限，
每个建模mutator及sender／queue／receiver／backing参与同一门，
F1 coeffect、F2 ENTER及F4 LEAVE按声明的有限足迹原子执行；
此外保留AS26.2的逐点有限原材料、原controller／prior计算终止、完整原输入及规定原确认条件，
当前source／record／port／connection权限独占有效，没有竞争写者、未建模写入、撤权或崩溃，
每个capture有F3的独立有限workspace、真实分stage traffic／genuine ACK与active本地进展。
则AS49–52的同一个有限 $J^+$ 安装，对AS49.4的整个ordinary域及准确mode10域满足以下结论。

在EnableCapture之后、吸收halt之前，每个真正到达的原或新增原语边界上的请求，
包括任意有限重复及每个有限嵌套森林，均可先于该边界的owed action有限进入并完成。
若 $H$ 是该请求ENTER之前的实际prefix，实际requester分别取得四个完整body，
每个单独解码为同一 $X(H)$，且各有AS52.2的实际space／time／boundary／memory含义。
所选received body的解码值进入真实控制字段回写及parent释放参数，
把同一个活动接回同一个pending action；该action在自己的原guard／input允许且有限后续干扰结束后恰执行一次。
如果原输入仍缺失，返回只保留其pending，不制造输入或假执行。

有限森林及原规定有限供应之后，原组件保留同一 $\xi$、根／parent／共享tapes、真正Y、
完整接受／拒绝、原records、原AfterFinal／Entry、Park／ParkACK、同一个HandbackPending，
并实际执行恰一次原Stop／INITIAL消费者、全部snapshot／verifier／receipt／output／ACK／token-return及global halt。
所有支持工作、先前sender effects、部分对象和共存材料均保留且在同次实际前态计费。
该结论的原子边界恰为F0–F4声明粒度，不包括尚未实现的更细基础内部。

证明。第54节证明真实局部记录与统一held-frame不变量；第55节由实际四份生产、完整traffic及实收字段回写给一次处理。
第56节证明该不变量在全部partial支持状态中闭合，并对任意有限森林作结构归纳。
第57节先建立原source投影，再应用AS36.4、37.1及真实终止消费者；第58节给精确同次账。
这些证明均不以父owed action先执行或原过程先完成为前提。$\square$

## 54. 自身也在目标内的真实记录与统一保持

**定理 54.1（真实局部记录归纳）。** 在F0–F1下，对从真实genesis开始的每个有限联合prefix $H$，
AS52.1从旧tail读取的fold恢复恰好 $X(H)$，包括日志本身、inventory、未初始化／未链接材料、
真实引用、当前权限描述及每个费用所需的实际前态。
本结论是数据恢复；使用恢复数据执行动作仍须有当前活的授权。

证明。对联合occurrence数 $m$ 归纳。$m=0$ 时只有F0声明的真实不可约入口及支持根，
其有限字段、当前授权和材料就是genesis；未知seed／code／input尚不在状态中。
初始基础材料的计费按第58.1节承担，不从未来日志读取其未有的字。

设已经恢复前 $m$ 项，考虑真实下一core $e$。
Native动作只读写相邻有限细胞／marks或有限latch／token／control，原receipt只添固定有限meter材料；
AA或支持规则只动其schema的有限字段／绑定／有限控制。
variable word／arithmetic／tree traversal的每一步都属于这些schema，不在归纳步中批量执行。
F1给出的tuple是这个真实occurrence的实际读数、选择、位置、结果、I/O origin和返回绑定，
故在已恢复前态应用该tuple恰得到真实core后态。
若刚分配对象尚未初始化或未链接，birth项已建立其真实identity及未初始化字段；
后续没有发生的初始化、seal或parent link不能由fold添入。

随后用该项携的真实node binding $j$，按固定规则创建其prev、payload、read／retention grant、
inventory entry及新tail。这些是已知有限规则的effects，不需要另一条“记录logger”的core。
从而连同原meter coeffect，联合步的整个后态均恢复。
真实j不能由payload值相等的另一个节点替代，inventory也记录actual birth而非逻辑root可达集。
下一项仍取这个新后态作前态，故别名、重复写入、refusal／test、sender／receiver的交错均保持。

由归纳恢复每个实际前态及其规则，故也恢复 $H$ 的全部已发生occurrences、rights变化及retained material。
按第58节在这些前态应用原／新tariff便得到 $C(H)$；没有从另一schedule借bill。
读旧tail时后续ENTER／扫描／输出的节点不在该链中，
所以无需让一个body描述自己将来的生产，也无需解自包含费用或无限logger方程。
因此fold恰为(AS49.1)。所有重放只在构造的数据图上发生，不改变live原源。$\square$

**定理 54.2（统一操作框架保持）。** 在F0–F4及合法traffic下，每次ENTER从 $p$ 选到新 $c$ 后，
直到匹配LEAVE前，$p$及更低ancestor的操作框架、所欠动作和当前活权限保持。
允许的行政回写逐项等于原保持值；公共日志、inventory、档案及累计账可以增长。
这个不变量不依赖 $p$ 的PC、对象完成性或活动栈高度。

证明。在ENTER前，所有persistent变量已在真实原组件或capsule／heap中。
ENTER只写其固定新capsule／key、selector和实际wake effect，不读写父运行环境。
它保存的是旧L及旧Active的真实绑定；$c.\mathsf{localRoot}=\mathsf{null}$ 本身就是完整定义的raw入口。

选中 $c$ 后，ancestor组都与Active不同。除ENTER外，每个实际mutator调用都受F2门控，
因此原driver、sender、queue、receiver及backing控制器均不能自行推进其所欠动作。
仅控制receiver并不足以得此结论；这里用的是全参与者前提。
新子工作与其peer处在新组，使用新workspace及连接，不读写原token owner或借用父scratch。
当前grant由custodian保留，没有因serialize或selector改变而转移成数据字。

child的普通工作只写自己的可变堆及公共追加状态。
行政写只在完成正确性检查之后取自实收切口context；由定理54.1及第55节的完整复制，
这些context值正等于进入时的保持值，所以写后框架相等。
此论证可连同第55.2节的字段循环逐步归纳，不须假定整个restore原子完成。
日志及inventory写在被排除的公共增长域，不影响父扫描已固定的输入尾。
child只可消耗自己的top key，ancestor key不能由普通字段写重置。

若中途再次ENTER，原Active就是这个partial child；同一论证把它的完整raw操作框架留在原处。
未完成link、occupied latch、半写字及parser next index都不是例外。
匹配LEAVE在同一个有限边中spend／retire／select父；不夹入其它ancestor动作。
归纳遍历实际occurrences便得不变量。
尤其不声称 $X$、全journal、inventory或账恒等于进入前值；它们确实包含新子活动的全部工作。$\square$

## 55. 四份实际生产及实收数据的运行返回

**定理 55.1（四条有价生产路径）。** 在定理53.2前提下，若一次请求期间不插入child，
AS51.2有限构造并真实交付四个独立完整body，各自满足AS52.3。
四body是同一旧cut的不同结构表达，其实际生产不依赖另一个已生产body。

证明。旧 $c.\mathsf{cut}$ 的prev链长有限，且每个节点有当前read／retention grant。
逐项读入构造栈、反转、序列化均为有限个字段／bit操作。
定理54.1保证从该真实链得到的每个effect、身份和未初始化状态均属同一个 $H$。
后续扫描产生的日志node只接在新L之后，不进入旧链。

time producer按正序输出每个tuple、实际node binding及有限schema信息。
space producer在自己的新workspace中对这个固定prefix逐项读取birth／endpoint条目，
为每个真实identity建立一个有类型顶点，为每个occurrence建立顶点及前驱spine；
依字段版本、read／write／grant、root／parent／channel关系写incident edges。
identity去重可以在已固定有限表中作全比较，不用原子lookup；同值body不引起identity合并。
一项重复引用连回同一顶点，reserved或unlinked对象仍由birth条目出现。

boundary producer在它自己的重建字段表上逐tuple推进，
为每个schema产生literal box及完整read／write／I/O terminals，
按实际identity和版本把前后对应字段连为carry wires，标出genesis和最后raw boundary。
某步的字段集及整个旧prefix都有限，所以逐项检查并写所有wire是有限程序；
不会在一条规则中复制whole world。
memory producer独立读取真实旧journal graph，输出每个实际node identity、prev和payload及genesis。
receiver取得的是这个真实graph的完整表示与复制品，不把destination allocation认同为原node。
每条路径均从自己的新Collect开始，不读取其它三份body或把它们的decoder当作输入来源。

每种结构可用固定tag、$U$、$B$、$T_r$及typed field序列化；
任意长整数及reference表示的逐bit处理属于F3操作。
四份destination在初始状态分离，各有独立真实mailbox／channel／peer backing。
对每个长度frame及body位置归纳：sender只有在正确阶段发送该位置实际bit；
receiver IN占用latch后，其backing写入同一个bit才开放下一位。
ending逐位匹配且完全exhaustion后才seal，因此每份完整destination逐bit等于对应真实sender块。
该复制归纳复用TMC PR57.D7／L4的排他所有权方法；
此字段机的操作数、渠道及分配不同，不借用旧 $8k+4$ 作为本程序总价。
相应genuine ACK按自己的通道与阶段完成，不能由别次的相同bit替代。

四producer的有限遍历、构造和copy在F3交通及本地进展下都完成。
AS52.3的四个明确逆因而各自从这份实际received body恢复 $X(H)$。
来源真实性由本段所用真实读取／写入／copy链给出，codec方程本身不供应这些链。
这证明实际取得与source meaning同时成立。$\square$

**定理 55.2（实收回写及一次释放）。** 在相同前提下，四份body交付后，
完整所选received body供应真实context回写操作数及LEAVE的parent参数，
返回同一个held活动的同一个owed action，不生成、复制或复活权限。

证明。requester的choice发生在四份完整取得之后；它发送所选实收块的全部字节，
receiver逐length、body、ending及规定确认过程接收，故再一次逐位置归纳给完整相同body。
Verify逐字段检查kind、source／install、旧cut、parent、grammar及exhaustion，
再与该种真实已发body作全比较。
因此成功解码 $\widehat X=X(H)$，不是一个仅有相同逻辑树或相同terminal answer的状态。

$\widehat p=\mathsf{Active}(\widehat X)$ 已在 $H$ 中存在。
每个运行context引用也已在 $H$ 中有真实birth／endpoint记录；
F3冻结到该cut的inventory包含这些entry，全字比较返回其真实typed binding。
扫描长度不追随新增journal／child allocations，当前读写授权另由custodian检查。
故identity字决定选择哪个已有binding，而不是把一个字cast为能力。
原token／ownership描述可被恢复为数据，但不能授权任何write或LEAVE。

Reinstate循环的归纳断言为：已经处理的context字段等于实收解码值，
尚未处理的字段及全部父heap仍等于进入值，next cursor指向实收表中下一项。
起点由定理54.2成立。处理一项时，值或引用目标只取自实收解码，
通过实际held endpoint写入；因 $\widehat X=X(H)$，该值也等于仍保持的进入值，故断言保持。
Native的head位置同样从实收字段选定真实mark cell并写1；
父head未移动，所选cell原已为1，其余marks未变，唯一head关系保持。
PC、latch、引用寄存器及sender／receiver的对应控制字段均按其typed schema如此处理。
这是一列可能很长的个别写，完全解析、位置取得及表示访问均计费。

循环结束后实际执行 $\mathsf{LEAVE}(c.\mathsf{key},\widehat p)$。
parent参数来自刚收到并解码的body；已发body的比较只给验证，不作为回写或parent的备用操作数。
原解释器及driver随后真正读取已写PC／latch／register／head继续运行，
所以数据在活执行路径上被消费，即使正确回写在值上幂等。

F4只在当前child、真实key、unspent及parent匹配时释放；
spend和选择parent同一个原子边完成，不执行父动作。
释放后这个key已经spent，且原child不再Active，不能再次通过同一guard。
child也无写权重置key或花掉ancestor key。
父的heap、控制、rights和连接未改变，所以下一次父occurrence仍为同一个owed primitive。
若它是pre-IN且genuine bit已经buffered，那个原sender effect及bit仍在，原IN只消费它一次；
若是post-IN／pre-WR，bit在原occupied latch，下一步仍为该WR，不再接收同一位或提早开放连接。
若原输入缺失，F3不补输入，原IN仍pending。
有限后续child只可再延迟它；森林耗尽且原guard允许时，原进展条件使该原occurrence执行一次。
返回不是把旧 $X(H)$ 整体写回，新的日志、账、子archives和spent key均继续保留。$\square$

## 56. 全部部分状态及任意有限嵌套的闭合

**定理 56.1（边界schema的自适用闭合）。** 定理54.2、55.2的frame及return关系适用于
AS49.4每个真正到达边界，包括每个新增handler内部，不要求其localRoot非null、对象sealed或父helper可调用。

证明。按下一规则的schema逐类检查，而非选一个有限深度样本集。
普通field／bit／control步之前与之后的全部persistent状态都已在capsule／heap中；
原子birth之后即有真实binding和未初始化字段，即使尚未写入parent link也由inventory及F1记录。
因此child可以捕获“已分配、未初始化”“已初始化、未链接”“部分framing、尚未seal”各状态。
它不以root可达或完成descriptor为枚举前提。

IN之后、backing之前，pending latch和对应WR cursor是raw状态；
全sender／receiver／queue门控阻止一侧独自改变parent connection。
partial loan保持每个token自己的真实owner，支持不用原池，故不要求父补齐十二TOK。
AA Reserve后的未链接材料、source template内部、header head先链接而tail尚空、
Maintain cursor及原INPUT／STACK两界都由真实局部tuple与实际控制恢复，不能用Ready图像取代。

Collect、Interpret、Emit、DeliveryACK、ReceiveSelectedBody、Verify及Reinstate都只有固定控制标签，
所有变量栈、剩余length、identity比较位置、下一个字段index及已完成写入都在当前parent数据中。
若child进入Reinstate中途，parent已经写过的低层context字段仍保留，
child的parent是这个partial restorer，先恢复并释放它，不能跳过它去释放更低的原活动。
它继续自己的下一项回写后，才可能调用自己的LEAVE。

ENTER只有F2规定的有限原子write set，无待完成的软件save prologue；
post-ENTER的新capsule即使localRoot=null也是下一个可捕获活动。
LEAVE也只有F4原子write set，post-LEAVE的请求以新Active为parent；
没有consume key后尚未enable parent的漏掉边界。
F1日志node发布是core的固定原子coeffect，没有另一个半发布的软件logger阶段；
其软件复制、比较及解析则全部属于前述普通可捕获steps。
这些基础原子之外的每个新增边界均已落入同一capsule／heap不变量。
若另一个实现细分这些基础，新增内部状态须另证对应；这里没有以无声明的mask删减软件cut。$\square$

**定理 56.2（每个有限森林的完成）。** 在定理53.2全部前提下，
每个有限请求森林均有限完成所有节点的四份取得、实收返回及原pending-consumer接续；
安装代码与engine数不随树高变化，实际frame／材料数可以增长。

证明。先不插child。Collect每步缩短固定旧prev链；反转、graph与box构造消费固定有限序列。
copy／parse／比较的输入为完整有限frame及冻结INPUT集合，identity查找消费固定inventory区间。
其内部栈虽可增长，每项代表该固定有限输入尚待处理的节点／字段；
逐项全扫描、按固定graph边或proper subspan推进给有限遍历，不把STACK增长并入INPUT。
引用所指parent在cut已出生，不需等待后来inventory entry。
每次bit交通及相应真实ACK均由请求自己的F3供应，所需本地动作有限干扰后进展。
所以第55节的一次无child处理有限完成，不等待ancestor ACK、原未来结果或借来的父pool。

对有限树的节点数作结构归纳。叶子就是上述无child情形。
设一个节点的所有child子树均已有结论。
每个child进入时，定理56.1保留这个节点当前partial状态；归纳假设使该child有限完成，
定理55.2返回这个节点的同一个owed action和同一个局部进展字段。
可以在证明父终止时收缩这一有限child片段。
收缩只去掉child占用的时间和追加公共材料，不去掉它的真实effects／账，也不回退实际世界。
父的局部循环界、旧tail、冻结inventory、frame长度及INPUT端点不受公共增长影响，
故其无child有限进展论证仍成立。

这个节点只有有限多个child，依其真实出现次序逐个收缩，得到父有限处理结束。
所得论证同样适用于正在return／reinstatement的parent，因为其next index等局部字段由同一frame保持。
最后按有限root次序组合便得整个森林完成。
归纳量是这次请求树的有限大小，没有预选最大深度；每次实际ENTER以新材料出生一个capsule／key。
一台固定engine只是反复选取当前capsule，不要求每层新executor。
该证明不推出无限请求流终止、统一有限硬件或统一latency。$\square$

## 57. 原来源投影、完整family与真正终止消费者

**定理 57.1（同一个实际组件的原投影）。** 在定理53.2前提及合法支持traffic下，
去掉支持动作／新增coeffects和暂时gate区间，保留每个原occurrence、genuine I/O、原backing、原record及其实际对象次序，
得到定义49.1那个原组件的一条合法执行。
反之，每条声明域内的原有限schedule可在足够材料及traffic下插入任意有限请求森林，
所以投影没有删掉ordinary的输入量词。

证明。对原occurrence的实际次序归纳。
开始时原boot按自己的真实输入、分配、初始化运行；F0只另装支持基础，
没有把已知AA alpha当作未知Native seed，四个原root都来自各自真实allocator return。
原source、tokens、port及记录字段保持其原语义；支持命名域与原非event对象分开。
每次支持进入仅保留运行frame，字段回写按第55.2节等于保持值，LEAVE不执行原动作。
故在下一个原occurrence之前，原操作数、PC、head、latch、当前授权及真实连接位恰为先前原effects所决定的值。
它的原guard／使能性、操作、response、source edit和原coeffects与相应未插入支持片段的步骤相符。

这包括先于receiver的每次真实sender OUT：它及其sender新control／backing留在投影，
不能从“未消费”删去发送，不能交换events制造相同bill。
原IN后的WR／status／seal、Refusal／BadFrame／disabled none等也保留原角色。
额外日志记录原步的真实effect，但不替原consumer发送Y、不代写source edge或原journal row。
因此每个投影step有原程序允许的实际前置和effects；被抹掉的支持区间只造成原字段上的stuttering。
新旧完整microhistory、identity描述及费用不被断言相等，额外档案在实际增广执行中继续存在。

反向在原schedule任意真正到达cut插入请求。
ENTER不需要先执行该cut动作，第56.2节给该有限森林的完成，返回后同一个原动作仍有原前置。
依次插入有限多个root即得增广执行。不同 $N$、树大小、guards及adaptive选择都不影响安装表。
所以得到的是同一真实来源的保守操作对应，不是由一个body相同的模拟source替代它。
原no-interrupt假设是在该投影中满足，不能直接对含支持嵌套的完整chronology调用原完成定理。$\square$

**定理 57.2（完整普通域、准确legacy与终端）。** 在定理53.2前提下，
有限森林之后的原组件按AS36.4及37.1完成AS49.4的完整输入域，
每个Entry仍有source $E(t_i)$、实际 $h=K=w(t_i)$ 及真正Y选择的同一个actual descriptor。
最终Park、原handback及INITIAL输出在同一实际运行中恰一次完成。

证明。先由定理57.1建立可用原完成结果的投影。
AS28.4给真实Init、initial carrier及 $\mathcal R_0$，不是预设一个完成入口。
AS36.2按每个前一全response／settlement之后真正供应的下一modifier及独立guard推进到 $\mathcal R_{i+1}$。
全部原raw candidate／refusal、Plan／Reserve／Raise、arena／Build／Tag、原parser／MUX／ordered STORE、
真正Y、全J／U、indices／sidecar／dependencies、source TOK／idle、新response-state及完整settlement均在投影中实际发生。
AS34.4的全M／ACK／Done／carrier及SAME new response-state reload之后才执行原AfterFinal、反向TOK及Entry。
嵌套支持不能用预测Plan位替代Y，不能让下一speculative edit越过前次全ACK。
归纳覆盖任意有限 $N$ 及依先前真实acquired responses的adaptive选择；$N=0$用原initial carrier直接finish。

legacy只应用AS37.1的准确原域：C1 guard2拒绝而保O，guard4接受而选F；
前者C2为Right(alpha)，guard2拒绝、有限guard至少3接受，
后者C2为Rho，guards4、5拒绝、有限guard至少6接受。
C2入口始终晚于C1全结算／AfterFinal／Entry／Select。
额外 $r_0$ 在legacy仍是真实distinct alpha／idle材料，不与O／F／N*认同。
mode00／11及各原拒绝／局部退出／故障标签按其原图保留，不由ordinary结论扩张策略域。

真实finish先按AS35.1保存原HandbackPending，完成Park及全ParkACK echo，
再新Close29重载这个SAME HandbackPending，执行原十二反向TOK及Handback。
AS35.2与RG9.1–9.2的真正configuration／waiting字全copy、真实table24定位、
invocation转交及新loan把实际原解释器带到原Stop；它真实写／seal $(0,B,1)$，
经49完整输出及dependencies，再完成Halt row、J／U、48交付、冻结indices及SEG-P1。
50到verifier的全snapshot、枚举／prior／INITIAL检查、accepted SEG-R1、
51到consumer的全bindings／receipt、43目标全copy／OUT及全部ACK／tokens都保留。
这些段仍可在各prehalt边界插入有限capture；第56节保证返回的consumer正是该段所欠动作。
原invocation仅离开RG一次，terminal图没有回RG边，吸收global halt同时禁用ENTER与支持执行。
故原INITIAL-$q_1(\beta)$消费及global halt恰一次，不增添posthalt reentry。$\square$

**命题 57.3（真实部分切口的对应）。** 定理53.2在下列实际原cut及支持cut上保留各自原consumer，
这些对应是统一定理的应用，不是以若干样本替代全域。

证明。AS28.2在十二TOK到InitForward的第一TOK之后，原pool owner分裂，所欠为第二TOK。
F2保持这一个分布，child使用自己的F3 arena，释放后仍到第二TOK，不使原helper在部分借用时运行。
AS34.3的genuine ACK IN之后、backing WR之前，先前OUT与IN均在journal，
位在occupied latch，连接没有开放；child返回该WR，不把状态写成缺input或重新IN。

AS46.1的真实first-$P_R$仍是当前cone上的相对Do$(P,\varepsilon)$，即全局 $P_R$。
Reserve已供cell，Maintain先写head再写tail；两个原cut的tail／control及AA费用差别由F1的那次实际AA字段事件记录。
这里没有用相同Native stamp猜AA状态，也没有重证AS47.1的现有client非因子化。
$J^+$ 的当前观察map因真实新增日志／授权而改变，不能把旧等观察结论无条件搬到新安装。

支持allocation后未link、selected receive后未back、Verify扫描中途及Reinstate部分写后，
child均保持当前partial capsule的真实cursor、字段与owed action。
pre-LEAVE时保持同一个尚未spent key，post-LEAVE时请求的新parent已是新Active。
这些分别直接代入定理54.2、56.1，均不先补齐parent步骤。$\square$

## 58. 同次实际前态的全部费用与同时保留

**定义 58.1（坐标及入口材料）。** 费用取非负向量，按owner／purpose／opcode分开：
原Native、原AA、auxiliary field／bit／I-O／control、行政写、grant／capability访问、
gate比较、ENTER、LEAVE、journal birth／backing及实际reference-bit访问各有坐标。
不设任意标量兑换率。设 $C_{\rm gen}$ 为F0不可约有限基础的显式供应／材料费用，
原不可约材料亦列在相应入口坐标；若从计费入口开始列历史，把这一固定项作为入口项 $e_0$ 计入。
没有从“不可约”推论“免费”，也没有把支付它当作已证明实际可用。

对后续联合步 $e$ 及其实际前态 $z$，定义

$$
\delta(e,z)=\delta_{\rm core}(e,z)+\delta_{\rm gate}(e,z)+\delta_J(e,z).
\tag{AS58.1}
$$

原core用其原Native／AA tariff，支持core用下述明确操作计数及真实字段／bit量。
若某具体模型为这些新坐标给定非负价格函数，下列关系对该函数逐项精确成立；
这里不给未规定价格虚构whole-run数值。

**定义 58.2（新增动作的逐项tariff）。** READ／WRITE／TEST／ALLOC／finite-control／bit-IN／bit-OUT／local-ACK
各在其命名auxiliary坐标记一次，并计全部实际读写字段、比特、引用表示及构造schema／backing材料。
word copy、整数计算、seek、full comparison、framing、length cursor、status／seal和cleanup是这些实际occurrences之和。
held-context写另计行政写及其bit／reference访问；inventory全扫描、完整identity比较及当前capability检查分别收费，
不设一个单位价Resolve隐藏其中工作。

ENTER计一次enter、两个固定schema对象birth、AS50.1的全部capsule／key初始化、
selector／wake字段访问、真实sender effect、当前grant及gate比较、实际reference表示，随后计其F1 journal。
LEAVE计一次leave、实际key／top／parent全比较、spent／retired／selector字段写及表示访问，随后计journal。
父动作未发生时不计虚构的原action receipt；它真正发生时再按原tariff计费。
每个受门控的实际调用承担其binding equality及guard字段访问，固定gate／wire／grant材料另在安装计入。
缺input的disabled状态本身不制造一次IN、原receipt或收到的bit。

journal coeffect记一次node birth，并计实际 $b_J(e,z)$ bits的schema／tag／prev／effect backing、
实际reference宽度、所复制字段位、read／retention grant／inventory登记及tail访问。
$b_J$ 是这一次真实固定schema tuple的表示长度，字段元数有界不使它成为统一常数。
节点自己的birth／grants／links由这一coeffect收费一次，不再递归启动logger；
日后把节点读成body或复制又是另外的普通工作。

boot计全部真实boundary／cell／code／control／type／endpoint／grant bit及安装动作，
包括四根／原Native准备／saved client／Lift及F0基础。
每个capsule的channel／peer／backing、四份独立遍历／body／mailbox／destination、
完整selected-body重传／ACK、解析／比较、当前authority检查、个别回写、retired key／frame及清理均计入真实occurrences。
没有从旧copy-loop、另一个engine或另一次schedule借常数或bill。

**定理 58.3（精确同次加法与peak）。** 对定理53.2的一条实际有限历史
$H=(z_0\xrightarrow{e_1}\cdots\xrightarrow{e_m}z_m)$，令

$$
\begin{aligned}
C(H)&=C_{\rm gen}+\sum_{i=1}^{m}\delta(e_i,z_{i-1}),\\
P(H)&=\max_{0\le i\le m}S(z_i).
\end{aligned}
\tag{AS58.2}
$$

若后继 $\tau=(z_m\xrightarrow{f_1}\cdots\xrightarrow{f_r}z_{m+r})$ 实际发生，则

$$
\begin{aligned}
C(H;\tau)&=C(H)+\sum_{j=1}^{r}\delta(f_j,z_{m+j-1}),\\
P(H;\tau)&=\max\{P(H),\max_{0\le j\le r}S(z_{m+j})\}.
\end{aligned}
\tag{AS58.3}
$$

其中 $S(z)$ 将每个实际allocation只算一次，包含原source／mandatory backing／archives及constructed capacity，
固定支持代码／endpoint／grant、全部journal node／inventory、live及retired capsules／keys／channels／peers，
四body及copy archives／selected-body backing、全部partial parent／child work和原terminal材料。

证明。每个实际联合occurrence按(AS58.1)在自己的真实前态贡献一次，拼接仅分开同一有限和的索引。
入口费用只有一份，后段不再收费一次 $C_{\rm gen}$；若以 $e_0$ 表示入口，则第一式也就是包含 $e_0$ 的逐项和。
有限最大值的索引分成旧段与新段即得第二式。
共享引用不重复计同一个allocation，但四个独立body／mailbox／destination是真实不同allocation，不能按字相等去重。
child工作时，所有held ancestor的实际材料与child、journal、旧archives同时存在，
因此它们在那个 $S(z)$ 中相加，再沿同一history取最大；不能把分别达到的peaks相加或挑另一run的低点。
清scratch可改变live值，不退已构造capacity；LEAVE不撤销records、sender effects或任何已收费动作。
全部坐标非负，故返回也不重置账。$\square$

**命题 58.4（原计数与有限性边界）。** 若 $n_N(H)$ 是这条真实增广prefix中的原Native core数，
则原Native receipt／tick／fee仍分别为 $n_N,n_N,2n_N$，其构造材料沿AS38.1为

$$
S_{0,N}+b_{{\rm control},N}+8A_{{\rm nonmeter},N}+8n_N.
\tag{AS58.4}
$$

这不是整个 $J^+$ 的材料或总价。每个定理53.2所涵盖的有限实例具有有限工作与材料，
但没有由此得到统一有限容量、polynomial bound、固定reference宽度或资源优势。

证明。每个原Native core仍有原固定receipt coeffect，与新增支持动作坐标分开。
所以逐次增加一receipt、一tick、二fee；ordinary cell与meter的八bit表示给(AS58.4)，已计为cell的code不再重复计。
AA动作不会因新全actor journal而被改计成Native occurrence；
其原allocation／grant／fields／navigation／I-O／ACK／control及reference-bit工作分别保留。
AA22.1的 $V=1+P+2S$、$S$ headers及 $D$ appends仍只是各真实root／完成局部段上的located subcounts，
不是任意partial cut的免费counter或whole tariff。
第56节给每个有限森林有限步，原finite schedule由第57节完成，
每步有限schema及实际有限reference表示只加有限材料，故该实例总量有限。
树高、operand、历史、嵌套receipt、inventory及表示宽度均可增长，
没有一个跨全部实例的数值界由这个逐点论证产生。$\square$

## 59. 来源、方法归属与仍须供应的关系

**定义 59.1（来源对应及方法适用域）。** 下表原primitive／source合同以
`9d9e025231cfb55c1268b799472e41b1b2f9d9e3` 的原文为对应，AS45–48按同卷现行字节使用。
各既有结论只在自己的实际安装与域上复用。

| 来源 | 在本构造中的准确角色 |
| --- | --- |
| AS1.2–1.4、26–29、34–38、41.1 | 原literal操作／连接、真实四根／Init／Build、完整ordinary及准确mode10、原pending-consumer规格与实际账；不自带F0–F4 |
| [TMC PR57.D1／(PR57.03)、D7／L4](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | 固定局部足迹、真实head mark／input latch、原meter、有限control展开、完整immutable copy方法；meter不是private transcript |
| [AA20.1–20.3、22.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | 真实分配返回／当前字段权限、Reserve、pending append、link-before-tail及完整同根Return；原busy owner不自动向新client授权 |
| [CAP的十二TOK及latch合同](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md)、[RG9.1–9.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md) | partial loan保留、真实HandbackPending／Stop／INITIAL终端消费者；不把completed-boundary handback冒充任意busy capture |
| [OC2.1–2.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_CONTROL_HISTORICAL_ACQUISITION.md) | 显式新增行政endpoint、当前grant与有限coeffect的建模先例；其PC-only socket不是本联合来源的完整grant |
| [Sparse Entry10.1–10.3、14.1–14.2、23.1–23.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_NATIVE_ENTRY_ACQUISITION.md) | owner-local数据与实际collected observation的区别、unfinished-tail／raw状态及付费扫描边界；不推导本client已有busy read |
| AS43.1及46.1–48.3 | 既有K admission障碍与真实first-$P_R$可见性义务；本构造用明确新gate／日志离开其前提，不重计这些结果 |

有限codec／逆、graph序列化、完整复制、逐步record／reconstruction及有限树归纳为复用方法。
有限continuation constructor携全部free variables、一个apply dispatcher解释动态数据实例的背景见
Danvy–Nielsen, *Defunctionalization at Work*, BRICS RS-01-23，§§1.2–1.3、3.1，
[原文](https://www.brics.dk/RS/01/23/BRICS-RS-01-23.pdf)。
它只支持AS49.3／51.1的有限代码与数据环境组织，不产生中断入口、source grant或exact-once能力。
Kiselyov–Shan的[delimited continuations实例](https://okmij.org/ftp/continuations/ZFS/context-OS.pdf)，
DOI [10.1007/978-3-540-74255-5_22](https://doi.org/10.1007/978-3-540-74255-5_22)，
在已有scheduler／resource block／prompt下把action与continuation相连；其cooperative服务点不覆盖本任务全部busy边界。
本构造的有界真实journal、全参与者gate、实收值回写及线性selector规则需自己的上述证明。

record／replay只能在真实起点且相关实际input／effect全记录时使用；
ReVirt的真实VM checkpoint及外部非确定事件记录方法见
[Dunlap等原文§§4.1–4.2](https://www.usenix.org/legacy/events/osdi02/tech/full_papers/dunlap/dunlap.pdf)。
这不替代F0真实boot，不供应本模型权限、全部raw state或live return。
[seL4 13.0.0的thread接口](https://github.com/seL4/seL4/blob/13.0.0/manual/parts/threads.tex)也不作为实现桥：
unbind仍可能保留IPC queue接收，suspend含cancelIPC，自身register／unbind访问受限制；
F2明列sender／queue／backing全门控正是一个须另供的条件，不能从“thread不运行”推出。

关于中断验证的成熟save／restore及隔离思路，可参见Feng等
[*Certifying Low-Level Programs with Hardware Interrupts and Preemptive Threads*](https://flint.cs.yale.edu/flint/publications/aimjar.pdf)，
DOI [10.1007/s10817-009-9118-9](https://doi.org/10.1007/s10817-009-9118-9)，§2.1，
以及Chen等[*Toward Compositional Verification of Interruptible OS Kernels and Device Drivers*](https://flint.cs.yale.edu/flint/publications/device.pdf)，
DOI [10.1145/2908080.2908101](https://doi.org/10.1145/2908080.2908101)，§4.2.1–2。
其受保护scheduler／context区段及same-device masking不供应本任务的同服务全边界reentry，
也不构成禁止任意嵌套的通用定理。

本条件组合及第54–58节的同源对应归属repo-derived；上述成熟方法不另计新数学成果。
未作全球文献穷尽或新意认证，不主张新的通用编码／continuation／snapshot定理。
新内容为明确F0–F4之下，全原有限family、全部raw及支持内部cut的四份真实取得，
实收body的运行返回和有限森林闭合；其基础的可用性不在所证结论中。

**定理 59.2（条件结论的准确边界）。** 定理53.2保留完整原目标的量词，
只在F0–F4声明的增广理想模型中证明其当前供应部分；
它不证明未改装J-FAMILY已有这些基础，不给历史数据到当前权限的推论，
不解决更广策略／来源、实际无限运行、统一有限设备或global／Pareto最小性。

证明。F0–F4的真实委托、全mutator接线、原子边及材料供给在定理53.2中均作为前提，
证明没有从旧菜单构造它们的步骤；故支付费用不能消去可用性前提。
若漏记实际boot前已擦去的信息，定理54.1的归纳基不再是完整目标；
若一个sender／queue可绕gate改变held连接，定理54.2的frame不再成立。
若把ENTER／LEAVE／journal coeffect细分成多行，定理56.1逐schema论证未涵盖那些新内部状态，
须给新的source realization及closure证明。
这些是本证明具体使用的义务，不是对其它合法增广的普遍不可能结论。

AS52.3恢复的是 $\mathsf{Rights}(z_H)$ 的数据，实际回写与释放仍使用F3／F4当前custodian能力，
所以codec或历史权限本身没有成为新grant。
四种结构含完整event spine或internal terminals，并未证明只保留旧外部boundary或更少关系仍充分；
也未证明此结构在大小、权力、root数或全资源上最少。
第56节只对每个有限请求森林归纳，第58节只给逐点有限成本及同次精确关系，
不支持实际无限请求流、统一finite hardware／latency、总资源支配或物理价格结论。

AS40.3、44.3的既有结果保持原域：
[RCA15.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md)的finite-completion-conditional历史handler closure、
[IR的declared compiler-cut current结果](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMMUTABLE_INTERVAL_REGISTERS.md)、
[GENERAL15.5／18.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md)及RG13.3的既有cross-entry／inherited original-Q域均直接复用。
它们之外的changed／new rows、broader mixed interiors及full terminal-task kernel仍需各自证明；
本构造没有把它们自动移到新增journal／gate图。
更广internally generated independent guards、all-seven direct schedules、noncanonical／physical sources及更广实际alpha／beta到原consumer桥仍未供应。
原mode10并未因本定理变成任意internal policy。

其它有限概率共同来源／执行正规化、静态量子锥／效应或几何重构结论各有自己的模型，
不含本定理使用的当前grants、owner-bound activation、busy admission及pending-action字段；
它们不作为F0–F4的隐含来源。
因此空间／时间／边界／记忆最简关系结构及实际互恢复的完整持续目标仍未完成，
剩余可用性、实现粒度、原任务核和最小性义务均保持。$\square$

## 追加锚（本行以下为增补区）
