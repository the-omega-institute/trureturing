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
root在原活动的真正到达边界进入。每个请求occurrence均有AS50.3（F2）的当前源绑定wake权、
独立授权peer本次genuine one-bit handoff及有限进入材料，并有F3的后续实际合法有限framing／traffic／ACK／workspace。
这些是每次请求的实际供应，不从parent原input／ACK、工作池或完成事件借取。
F2统一量化AS49.4全部covered cuts：在任意这样一个cut均可供应上述授权请求，
不是先从cut域挑出已有wake位或已Ready的子集再定义森林。
森林只规定实际有限请求，不为一个无限请求流承诺终止，也不把树高或未来operand作为安装参数。

**定理 53.2（局部日志与保留活动的当前供应）。** 假定AS50.1–50.5全部成立：
真实记录从该组件自己的不可约boot入口开始，当前owner实际委托所有披露、门控、held-context权限，
每个建模mutator及sender／queue／receiver／backing参与同一门，
F1 coeffect、F2 ENTER及F4 LEAVE按声明的有限足迹原子执行；
此外保留AS26.2的逐点有限原材料、原controller／prior计算终止、完整原输入及规定原确认条件，
当前source／record／port／connection权限独占有效，没有竞争写者、未建模写入、撤权或崩溃，
并且对AS49.4每个covered cut、每个有限森林的每次请求，均实际供应F2的当前源绑定wake权、
独立授权peer的一次genuine one-bit handoff及fresh进入材料，使ENTER先于该cut的owed action可执行，
再供应F3的独立有限workspace、合法framing、真实分stage traffic／genuine ACK与active本地进展。
该统一供应不以原输入／ACK已到、原pool完整或parent已经完成为条件。
则AS49–52的同一个有限 $J^+$ 安装，对AS49.4的整个ordinary域及准确mode10域满足以下结论。

在上述逐请求wake及后续traffic实际供应下，EnableCapture之后、吸收halt之前，
每个真正到达的原或新增原语边界上的请求，
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

证明。先对任意covered cut用AS50.3的统一供应取得真实授权handoff；
其ENTER只动独立wake控制、fresh capsule／key及selector，故不先执行父owed action。
第54节证明真实局部记录与统一held-frame不变量；第55节由实际四份生产、完整traffic及实收字段回写给一次处理。
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
此时 $H=\varepsilon_{z_0}$、$L=\mathsf{null}$、$C(H)=C_{\rm gen}$、$S(z_0)=S_{\rm gen}$，
只包含第58.1节列出的入口材料及已给基础权；没有boot receipt或journal node。
初始费用从同一真实genesis及给定tariff确定，不从未来日志读取其未有的字。

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
以 $C_{\rm gen}$ 为唯一基项，按第58节在每个前态加该步core／gate／journal的互斥收费项便得到 $C(H)$。
对 $S$ 同样从genesis材料并入逐步实际出生的不同材料；旧材料上的读写只另计访问工作，不再计出生。
全部boot／安装也属于这些步，没有从另一schedule借bill或再加一份基础费。
读旧tail时后续ENTER／扫描／输出的节点不在该链中，
所以无需让一个body描述自己将来的生产，也无需解自包含费用或无限logger方程。
因此fold恰为(AS49.1)。所有重放只在构造的数据图上发生，不改变live原源。$\square$

**定理 54.2（统一操作框架保持）。** 在F0–F4及合法traffic下，每次ENTER从 $p$ 选到新 $c$ 后，
直到匹配LEAVE前，$p$及更低ancestor的操作框架、所欠动作和当前活权限保持。
允许的行政回写逐项等于原保持值；公共日志、inventory、档案及累计账可以增长。
这个不变量不依赖 $p$ 的PC、对象完成性或活动栈高度。

证明。在ENTER前，所有persistent变量已在真实原组件或capsule／heap中。
F2对这个cut供应的真实授权handoff不依赖父是否Ready或其输入是否已到。
ENTER只写其固定新capsule／key、selector和独立支持wake endpoint的实际有限effect，不读写父运行环境。
wake endpoint的专属控制与原sender及ancestor协议peer字段不同，按AS49.3属于公共支持域；
较早原sender／backing仍留在 $H$，其后果不被这个独立handoff改写。
它保存的是旧L及旧Active的真实绑定；$c.\mathsf{localRoot}=\mathsf{null}$ 本身就是完整定义的raw入口。

选中 $c$ 后，ancestor组都与Active不同。除ENTER外，每个实际mutator调用都受F2门控，
因此原driver、sender、queue、receiver及backing控制器均不能自行推进其所欠动作。
仅控制receiver并不足以得此结论；这里用的是全参与者前提。
新子工作与其协议peer session处在新组，使用新workspace及连接，不读写原token owner或借用父scratch。
固定wake endpoint只参加独立授权ENTER边；该边的有限效果与费用亦属真实 $X$，不冒称父框架上的零全局效果。
当前grant由custodian保留，没有因serialize或selector改变而转移成数据字。

child的普通工作只写自己的可变堆及公共追加状态。
行政写只在完成正确性检查之后取自实收切口context；由定理54.1及第55节的完整复制，
这些context值正等于进入时的保持值，所以写后框架相等。
此论证可连同第55.2节的字段循环逐步归纳，不须假定整个restore原子完成。
日志及inventory写在被排除的公共增长域，不影响父扫描已固定的输入尾。
child只可消耗自己的top key，ancestor key不能由普通字段写重置。

若中途再次请求，F2逐请求供应同样当前的wake权及这个新occurrence自己的真实handoff，
无须partial child先腾出连接或执行所欠动作；ENTER的原Active就是这个partial child。
同一论证把它的完整raw操作框架留在原处。
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

证明。任取AS49.4的边界，F2统一供应覆盖该cut的Active及partial状态，
故其真实wake handoff可先于owed action发生；没有用下面的状态分类筛掉未预存wake位的cut。
随后按下一规则的schema逐类检查，而非选一个有限深度样本集。
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

证明。先不插child。在任意请求cut按AS53.1／50.3供应当前wake权、该次独立handoff和fresh材料，
执行ENTER即可选中新capsule；这一步不等parent ACK、原输入、原完成或完整pool。
Collect每步缩短固定旧prev链；反转、graph与box构造消费固定有限序列。
copy／parse／比较的输入为完整有限frame及冻结INPUT集合，identity查找消费固定inventory区间。
其内部栈虽可增长，每项代表该固定有限输入尚待处理的节点／字段；
逐项全扫描、按固定graph边或proper subspan推进给有限遍历，不把STACK增长并入INPUT。
引用所指parent在cut已出生，不需等待后来inventory entry。
每次bit交通及相应真实ACK均由请求自己的F3供应，所需本地动作有限干扰后进展。
所以第55节的一次无child处理有限完成，不等待ancestor ACK、原未来结果或借来的父pool。

对有限树的节点数作结构归纳。叶子就是上述无child情形。
设一个节点的所有child子树均已有结论。
每个child请求时，F2的同一供应合同在这个实际partial cut仍给当前wake权及自己的genuine handoff；
ENTER不推进这个节点，定理56.1保留其当前partial状态。归纳假设使该child有限完成，
定理55.2返回这个节点的同一个owed action和同一个局部进展字段。
可以在证明父终止时收缩这一有限child片段。
收缩只去掉child占用的时间和追加公共材料，不去掉它的真实effects／账，也不回退实际世界。
父的局部循环界、旧tail、冻结inventory、frame长度及INPUT端点不受公共增长影响，
故其无child有限进展论证仍成立。

这个节点只有有限多个child，依其真实出现次序逐个收缩，得到父有限处理结束。
所得论证同样适用于正在return／reinstatement的parent，因为其next index等局部字段由同一frame保持。
最后按有限root次序组合；每个新root同样由该cut的F2授权handoff进入，便得整个森林完成。
归纳没有把后续F3 traffic当作ENTER的输入，也没有把一个wake位重复用作多个occurrences的handoff。
归纳量是这次请求树的有限大小，没有预选最大深度；每次实际ENTER以新材料出生一个capsule／key。
一台固定engine只是反复选取当前capsule，不要求每层新executor。
该证明不推出无限请求流终止、统一有限硬件或统一latency。$\square$

## 57. 原来源投影、完整family与真正终止消费者

**定理 57.1（同一个实际组件的原投影）。** 在定理53.2前提及合法支持traffic下，
去掉支持动作／新增coeffects和暂时gate区间，保留每个原occurrence、genuine I/O、原backing、原record及其实际对象次序，
得到定义49.1那个原组件的一条合法执行。
反之，每条声明域内的原有限schedule可在AS53.1逐次F2 wake／授权及F3材料／traffic供应下插入任意有限请求森林，
所以投影没有删掉ordinary的输入量词。

证明。对原occurrence的实际次序归纳。
开始时原boot按自己的真实输入、分配、初始化运行；F0只另装支持基础，
没有把已知AA alpha当作未知Native seed，四个原root都来自各自真实allocator return。
原source、tokens、port及记录字段保持其原语义；支持命名域与原非event对象分开。
ENTER所含wake sender effect只属于独立支持endpoint的专属控制，不是任何原sender或held ancestor的协议动作。
其真实handoff、较早支持发送／backing、origin、日志及费用全留在增广 $H$ 和 $X(H)$ 中；
投影去掉它们是按真实类型／endpoint的支持归属，不按bit相同或receiver尚未消费作删减。
每次支持进入仅保留运行frame，字段回写按第55.2节等于保持值，LEAVE不执行原动作。
故在下一个原occurrence之前，原操作数、PC、head、latch、当前授权及真实连接位恰为先前原effects所决定的值。
它的原guard／使能性、操作、response、source edit和原coeffects与相应未插入支持片段的步骤相符。

这包括先于receiver的每次真实sender OUT：它及其sender新control／backing留在投影，
不能从“未消费”删去发送，不能交换events制造相同bill。
原IN后的WR／status／seal、Refusal／BadFrame／disabled none等也保留原角色。
额外日志记录原步的真实effect，但不替原consumer发送Y、不代写source edge或原journal row。
因此每个投影step有原程序允许的实际前置和effects；被抹掉的支持区间只造成原字段上的stuttering。
新旧完整microhistory、identity描述及费用不被断言相等，额外档案在实际增广执行中继续存在。

反向在原schedule任意真正到达covered cut插入请求，不要求cut已Ready或已有wake位。
F0安装好的源绑定endpoint及持续授权、F2对每次请求实际供应的独立peer handoff和fresh材料
使ENTER在此cut可执行；F3再供应之后的traffic。较早原sender effects全部保留，缺原输入不被补入。
第56.2节给该有限森林的完成，返回后同一个原动作仍有原前置。
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

**定义 58.1（唯一入口分界及互斥收费项）。** 费用取非负向量，按owner／purpose／opcode分开：
原Native、原AA、auxiliary field／bit／I-O／control、行政写、grant／capability访问、
gate比较、ENTER、LEAVE、journal birth／backing及实际reference-bit访问各有坐标。
不设任意标量兑换率。固定同一组原／新tariff参数；未指定价格的坐标保留为实际计数／材料量或符号函数，
不给它们虚构whole-run数值。

唯一计费入口为 $z_0=\mathsf{genesis}$，在任何原或支持boot occurrence之前。
令 $\mathcal G$ 为此时实际已有的不可约材料集合：原Native primitive meter的两个boundary markers、
其固定primitive控制位，以及F0有限recorder／gate／bootstrap控制、基本活动／selector、
初始空journal／inventory所需的固定根、独立wake endpoint的primitive根及其基础typed bindings／grants表示。
只含这个有限入口确有的字段与规定常量；journal尾为null，没有journal node或已记occurrence，原meter有零receipt。
未初始化字段仍未初始化。literal支持程序、安装后的grant／连接backing、普通tape boundaries、
四个AA根／drivers、$O$七事件、Native未知seed／code／input／saved client及Lift／Init均不在 $\mathcal G$ 中，
它们的实际构造／接收／初始化必须出现在后续历史里。

$C_{\rm gen}$ 恰是供应这批 $\mathcal G$ 的入口材料／基础供应向量，$S_{\rm gen}=S(z_0)$ 是它的实际保留量。
没有由入口模型描述出一个未执行的物理制造过程、tick、receipt或journal事件。
本卷一律写 $H=(z_0\xrightarrow{e_1}\cdots\xrightarrow{e_m}z_m)$，
其中 $e_i$ 是入口之后真实发生的联合occurrence，包含全部支持安装和原boot。
不把 $e_0$ 作为可执行／可记日志的原语；若发票把入口列作一行 $e_0$，
该行仅是 $C_{\rm gen}$ 的别名，不在 $H$ 内、不参加 $\delta$ 求和，也不再另加一次。

对每个实际材料单位（包括固定对象的字段／reference backing及后来扩展的细胞／位）按真实birth归属分区：

$$
\mathcal A(H)=\mathcal G\;\dot\cup\;
 \mathop{\dot\bigcup}_{i=1}^{m}
 \bigl(\mathcal A_i^{\rm core}\;\dot\cup\;
       \mathcal A_i^{\rm gate}\;\dot\cup\;\mathcal A_i^{J}\bigr).
\tag{AS58.1a}
$$

这里 $\mathcal A_i^q$ 只含该步相应部分实际新构造／供应的材料；没有新材料的部分取空集。
对象后来扩展时只有新增部分入新的集合；同一材料的别名、初始化或覆盖写不再成为一次birth。
旧材料上的实际read／write／grant检查仍有操作／访问费，不能因没有新birth而省略。
若不可约基础已有一个endpoint根，之后构造它的code／grant表示或backing仍逐项计后来的新材料与全部安装操作，
但不再次供应那个已有根。

对实际后续联合步 $e$ 及其真实前态 $z$，定义

$$
\delta(e,z)=\delta_{\rm core}(e,z)+\delta_{\rm gate}(e,z)+\delta_J(e,z).
\tag{AS58.1}
$$

这三个项也按实际动作角色互斥分配：core含原规则或支持规则的本体及原Native receipt coeffect；
gate只含该次invocation的自动组绑定／当前wake权等门控guard检查；
$J$只含F1新增node、字段、read／retention grant、inventory登记与tail更新的coeffect。
ENTER／LEAVE本体的handoff、capsule／key／selector写归core，其自动门检查归gate，F1记录归 $J$。
软件显式inventory／capability检查是另一个收费的支持core，不与自动gate检查认同。
每个实际访问或构造项恰归一处，旧Native receipt不再列入新增journal费；
$C_{\rm gen}$ 的供应项不属任一后续 $\delta$。不同opcode次数、访问位量与材料量是不同向量坐标，
不是把同一次材料供应在两个来源中重复收费。

**定义 58.2（新增动作及全部boot的tariff）。** READ／WRITE／TEST／ALLOC／finite-control／bit-IN／bit-OUT／local-ACK
各在其命名auxiliary坐标记一次，并计其全部实际字段／比特／reference访问及属于该步的实际新材料。
word copy、整数计算、seek、full comparison、framing、length cursor、status／seal和cleanup是这些实际occurrences之和。
held-context写另计其行政写／访问坐标；inventory全扫描、完整identity比较及当前capability检查分别按实际步骤收费，
不设一个单位价Resolve隐藏其中工作。

ENTER的core计一次enter、两个固定schema对象birth、AS50.1的全部capsule／key初始化、
selector／wake字段访问及独立wake peer的真实sender effect与reference表示访问；其自动guard仅在gate项收费。
LEAVE的core计一次leave、其本体key／top／parent访问、spent／retired／selector字段写及表示访问，
自动使能检查仅在gate项收费；每一实际访问按58.1的角色只计一次。
两者随后各有自己的F1 journal项。原输入或parent ACK不供应wake，已经发生的各自sender／backing步骤另按所属原或支持core计费。
父动作未发生时不计虚构的原action receipt；它真正发生时再按原tariff计费。
固定gate／wire／grant材料中，入口已有部分只在 $C_{\rm gen}$，后续安装部分只在实际安装步中计入。
缺input的disabled状态本身不制造一次IN、原receipt或收到的bit；实际执行的测试／失败检查仍按其规则收费。

journal项计一次node birth，并计实际 $b_J(e,z)$ bits的schema／tag／prev／effect backing、
实际reference宽度、所复制字段位、read／retention grant／inventory登记及tail访问。
$b_J$ 是这一次真实固定schema tuple的表示长度，字段元数有界不使它成为统一常数。
节点自己的birth／grants／links由这一coeffect收费一次，不再递归启动logger；
日后把节点读成body或复制又是另外的普通工作。

boot不是另加的固定价，而是 $H$ 中从 $z_0$ 起实际boot／安装occurrences的同一 $\delta$ 之和。
它包含全部后入口boundary／cell／code／control／type／endpoint／grant的真实构造、接收、安装及访问，
四根／原Native准备／saved client／Lift、独立wake接线及EnableCapture均按自己的实际步骤计入。
这些步不重新收取 $\mathcal G$ 的供应费；若访问或初始化入口已有字段，只收实际发生的访问／初始化工作及新扩展材料。
每个capsule的channel／peer／backing、四份独立遍历／body／mailbox／destination、
完整selected-body重传／ACK、解析／比较、当前authority检查、个别回写、retired key／frame及清理也如此计费。
没有原或支持材料、安装工作或较早sender effect因入口分界而消失，
没有从旧copy-loop、另一个engine或另一次schedule借常数或bill。

**定理 58.3（全prefix的精确同次加法与peak）。** 对定理53.2的一条实际有限历史
$H=(z_0\xrightarrow{e_1}\cdots\xrightarrow{e_m}z_m)$，令

$$
\begin{aligned}
C(H)&=C_{\rm gen}+\sum_{i=1}^{m}\delta(e_i,z_{i-1}),\\
P(H)&=\max_{0\le i\le m}S(z_i).
\end{aligned}
\tag{AS58.2}
$$

对一条从任意实际出口 $z$ 开始的后续片段定义增量 $\Delta C(\tau;z)$ 为其中各联合步的同一 $\delta$ 之和，
不含 $C_{\rm gen}$。若
$\tau=(z_m\xrightarrow{f_1}\cdots\xrightarrow{f_r}z_{m+r})$ 实际发生，则

$$
\begin{aligned}
C(H;\tau)&=C(H)+\Delta C(\tau;z_m)
          =C(H)+\sum_{j=1}^{r}\delta(f_j,z_{m+j-1}),\\
P(H;\tau)&=\max\{P(H),\max_{0\le j\le r}S(z_{m+j})\}.
\end{aligned}
\tag{AS58.3}
$$

$S(z)$ 将当时实际保留的材料／constructed capacity按58.1的birth分区各算一次，
包括仍保留的genesis、原source／mandatory backing／archives、固定支持代码／endpoint／grant、
全部journal node／inventory、live及retired capsules／keys／channels／peers、独立wake endpoint控制及其backing、
四body及copy archives／selected-body backing、全部partial parent／child work和原terminal材料。
材料费用是供应／构造流量，$S$是同一材料的保留存量；取peak不再给它加一次供应费。

证明。空prefix $H=\varepsilon_{z_0}$ 时，$C(H)=C_{\rm gen}$、$P(H)=S_{\rm gen}$，
无occurrence、receipt或journal node。第一个安装步从此真实 $z_0$ 计费，
只把它的新材料及工作加入后续项，不重复入口供应。以后每步由58.1的互斥分区归属一次；
F1 coeffect和core同属这一步，其自身材料／登记／写入也只在 $J$ 项出现一次。
AS54.1的fold从同一genesis起恢复这些实际前态、birth归属及tariff参数，
因此恢复的 $C$ 正是(AS58.2)，包括pre-enable的全部安装及后来的wake／peer工作。
拼接仅分开同一有限和的索引，不把后段当作第二次从genesis启动的运行。
空后段有 $\Delta C=0$；在boot中途、恰好EnableCapture、ENTER／LEAVE前后或halt之后截取均使用同一分界。
若后段含真正halt，计其core、原receipt（适用时）及F1 coeffect一次；吸收halt之后只有空合法后段。

有限最大值的索引分成旧段与新段即得peak拼接式；共同出口在两个最大值中出现不引起材料相加。
共享引用不重复计同一材料，但四个独立body／mailbox／destination是实际不同allocation，不能按字相等去重。
child工作时，所有held ancestor材料与child、journal、旧archives同时存在，
因此在那个 $S(z)$ 中按不同材料相加，再沿同一history取最大；不能把分别达到的peaks相加或挑另一run的低点。
清scratch可改变live值，不退已构造capacity；LEAVE不撤销records、sender effects或任何已收费动作。
全部坐标非负，返回不重置账，历史入口也不会因retired capsule而再次收费。$\square$

**命题 58.4（原计数与有限性边界）。** 若 $n_N(H)$ 是这条真实增广prefix中的原Native core数，
令 $b_{{\rm control},N}(H)$ 为截至该cut实际已构造且未另列为细胞的原control／code位量，
$A_{{\rm nonmeter},N}(H)$ 为截至该cut实际构造的原nonmeter细胞数；两者不预计尚未安装的部分。
则原Native receipt／tick／fee仍分别为 $n_N,n_N,2n_N$，其构造材料沿AS38.1为

$$
S_{0,N}+b_{{\rm control},N}(H)+8A_{{\rm nonmeter},N}(H)+8n_N(H).
\tag{AS58.4}
$$

这不是整个 $J^+$ 的材料或总价。每个定理53.2所涵盖的有限实例具有有限工作与材料，
但没有由此得到统一有限容量、polynomial bound、固定reference宽度或资源优势。

证明。每个原Native core仍有原固定receipt coeffect，与新增支持动作坐标分开。
所以逐次增加一receipt、一tick、二fee；ordinary cell与meter的八bit表示给(AS58.4)，已计为cell的code不再重复计。
AA动作不会因新全actor journal而被改计成Native occurrence；
其原allocation／grant／fields／navigation／I-O／ACK／control及reference-bit工作分别保留。
(AS58.4)中 $S_{0,N}$ 属genesis存量，后续 $b_{{\rm control},N}$、ordinary cells及receipts按真实安装／birth归属；
空prefix时后三项均为零；这是保留材料的分类恒等式，不在 $C_{\rm gen}$ 和boot增量之外另收费一份。
AA22.1的 $V=1+P+2S$、$S$ headers及 $D$ appends仍只是各真实root／完成局部段上的located subcounts，
不是任意partial cut的免费counter或whole tariff。
第56节给每个有限森林有限步，原finite schedule由第57节完成，
每步有限schema及实际有限reference表示只加有限材料，故该实例总量有限。
树高、operand、历史、嵌套receipt、inventory及表示宽度均可增长，
没有一个跨全部实例的数值界由这个逐点论证产生。$\square$

## 59. 来源、方法归属与仍须供应的关系

**定义 59.1（来源对应及方法适用域）。** 下表原primitive／source合同以
`9d9e025231cfb55c1268b799472e41b1b2f9d9e3` 的原文为对应；
AS41–48统一引用同卷现行且属于保护前缀的
`ab9261a8d2617d1ae873ce8152950be302349863` 字节。
AS41–44在两pin之间逐节字节相同，AS45–48不在旧9d9e文本内；不把后者归到旧pin。
下表将原合同与这些current请求规格／障碍定位分开，各结论只在自己的实际安装与域上复用。

| 来源 | 在本构造中的准确角色 |
| --- | --- |
| AS1.2–1.4、26–29、34–38（9d9e原合同） | 原literal操作／连接、真实四根／Init／Build、完整ordinary及准确mode10与实际账；不自带F0–F4 |
| [TMC PR57.D1／(PR57.03)、D7／L4](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | 固定局部足迹、真实head mark／input latch、原meter、有限control展开、完整immutable copy方法；meter不是private transcript |
| [AA20.1–20.3、22.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | 真实分配返回／当前字段权限、Reserve、pending append、link-before-tail及完整同根Return；原busy owner不自动向新client授权 |
| [CAP的十二TOK及latch合同](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md)、[RG9.1–9.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md) | partial loan保留、真实HandbackPending／Stop／INITIAL终端消费者；不把completed-boundary handback冒充任意busy capture |
| [OC2.1–2.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_CONTROL_HISTORICAL_ACQUISITION.md) | 显式新增行政endpoint、当前grant与有限coeffect的建模先例；其PC-only socket不是本联合来源的完整grant |
| [Sparse Entry10.1–10.3、14.1–14.2、23.1–23.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_NATIVE_ENTRY_ACQUISITION.md) | owner-local数据与实际collected observation的区别、unfinished-tail／raw状态及付费扫描边界；不推导本client已有busy read |
| AS41.1、43.1及45–48（上述ab9261 current字节） | 全cut／pending-consumer请求规格、既有K admission障碍与真实first-$P_R$可见性义务；本构造用明确新gate／日志离开其前提，不重计这些结果 |

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

证明。F0–F4的真实委托、全mutator接线、每个cut可供应的当前授权wake handoff、原子边及材料供给
在定理53.2中均作为前提，
证明没有从旧菜单构造它们的步骤；故支付费用不能消去可用性前提。
若漏记实际boot前已擦去的信息，定理54.1的归纳基不再是完整目标；
若一个sender／queue可绕gate改变held连接，定理54.2的frame不再成立。
若某个covered cut不能供应当前授权独立wake，F2统一供应前提就不成立；不能把该cut从AS49.4删掉，
也不能以父ACK或较晚完成替代本次handoff。这仍是新增理想基础的可用性边界，其实际可用性未被证明。
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
## 60. 缩减效果采样器的同源模型与完整量词

**定义 60.1（新的自身入口增广）。** 以下记 $J_r$ 为同一个实际J-FAMILY组件 $J$ 的一种新增广。
$J$ 的含义仍为AS26–40；AS49–52及本卷53–59的全效果披露增广仍记 $J^+$。
$J_r$ 保留后者的有限活动机、全参与者门控、held-context行政权限和线性返回，
将其F1全效果披露替换为第61节的缩减记录，并安装第62–63节的具体独立唤醒源律。
本节不把这个源律归入旧AS50.1：旧式给出capsule、key与selector赋值，
其sender效果在AS50.3中另由handoff合同及全效果披露承担。

载体仍是唯一实际准备 $\xi$、原Native beta seed、代码、saved client、原source与STORE，
以及实际端口0–77、工作池1–12、受保护的16／17／25／27／74、48–51路线及五条外层连接。
四个AA根 $O,F,N^*,r_0$ 是四次实际分配返回的互异对象；固定driver、根槽、非null cone parent及共享祖先tapes均保留。
支持类型、分配域、端点和工作区另设。相等body、相同名字或相同计数不建立源身份，
尤其不把AA的初始alpha认作Native的初始beta。

**定义 60.2（全原域与全部切口）。** 安装是先于未来输入的一次固定有限安装。
ordinary域为每个有限 $N\ge0$、每个实际adaptive序列

$$
A_i\in\{\mathsf{Rho},\mathsf{Left}(v_i),\mathsf{Right}(v_i)\},
\qquad 1=g_0\le\cdots\le g_N<\infty,
$$

其中 $v_i$ 是在原raw ingress实际收到的任意非空有限有序树，
$g_i$ 在独立原GuardIngress真正收到，并保留genuine finish。
adaptive选择可消费以前真正取得的完整response，不能预知尚未收到的输入。
沿原AS26.1的候选函数定义

$$
t_0=\beta,\qquad
\varepsilon_i=[n(c_{A_i}(t_{i-1}))\le g_i],\qquad
t_i=
\begin{cases}
c_{A_i}(t_{i-1}),&\varepsilon_i=1,\\
t_{i-1},&\varepsilon_i=0.
\end{cases}
\tag{AS60.1}
$$

每个完整Entry的source为 $E(t_i)$，$h=K=w(t_i)$，descriptor由真正Y选择。
mode10仍恰为AS26.3、37.1：C0 guard2；C1 guard2或4；
C1完成全settlement／ACK、AfterFinal、Entry及Select之后才有C2。
C1拒绝时保留O，C2为Right(alpha)，guard2拒绝、每个有限guard至少3接受；
C1接受时选择F，C2为Rho，guard4或5拒绝、每个有限guard至少6接受。
$r_0$ 仍是未触动的alpha／idle，与其余三根不同。
mode00／11、原局部退出和fault边保留；没有加入任意internal policy或all-seven schedule。

付费EnableCapture完成后、吸收halt之前，每个真正到达的原或支持原语边界都是covered cut。
这包括部分Init／十二TOK、birth后未初始化／未链接／status0、Reserve／Maintain，
所有sender／queue／receiver／ACK／latch／backing阶段，原INPUT与独立STACK，
candidate、F7、holder、association、settlement、Park及全部terminal阶段；
也包括每个collector、evaluator、encoder、copy、checker、resolver、partial restorer，
以及ENTER／LEAVE紧前和紧后，特别是post-ENTER且localRoot仍为null的边界。
请求须能先于该cut同一个owed action进入；已使能且有buffered genuine bit的原IN也不例外。
缺原输入时返回不制造输入。

量词为每个有限有序请求森林：root数、每层宽度、高度、重复次数均可为任意有限值。
每个node在其parent真正到达的cut进入。安装不含未来 $N$、operand、guard、树高或请求数。
只有本模型明确保留的ENTER、LEAVE、原receipt及固定journal coeffect内部不增设cut；
其余软件原语边界一个不删。

**定义 60.3（raw目标、活动与保持范围）。** raw状态 $z$ 是完整有限typed实际对象映射：
含身份与alias、code／PC／control／latch／reference／mark／adjacency、
roots／parents／headers／tapes、pending edit／loan、当前rights，
连接位与origin、backing及阶段、INPUT与STACK、所有原和支持records／archives。
对象从实际birth起出现；未初始化、null、空位和已初始化零是不同状态，
未发生的seal、Done、输入和结果不预填。

令 $H=(z_0\xrightarrow{e_1}\cdots\xrightarrow{e_m}z_H)$ 为从真实入口开始的有限联合历史，定义

$$
X_r(H)=\bigl(H,z_H,\mathsf{Rights}(z_H),C(H),\mathsf{Ret}(z_H)\bigr).
\tag{AS60.2}
$$

这里 $H$ 含完整派生的实际core效果、读／写／测试／控制terminals、I/O来源、
同值写、refusal、旧receipt和新coeffect；实际journal却只存第61节允许的缩减项。
目标是ENTER之前的prefix，不含随后为表达它而发生的生产。

活动为基本活动 $b$ 或capsule。沿用AS49.2的十八个数据字段

$$
(\mathsf{parent},\mathsf{cut},\mathsf{peer},\mathsf{key},\mathsf{localRoot},
 \mathsf{pc},r_1,r_2,r_3,r_4,\ell_1,\ldots,\ell_8).
\tag{AS60.3}
$$

前五项和四个寄存器是引用或null，PC和八个latch取固定有限字母表；
任意长计数、路径、栈、环境、cursor均在实际heap中。
只有一个有限引擎，不按深度增加代码或引擎。
所有原参与者的组为 $b$，支持session的组为其capsule；独立ENTER以外的调用要求调用者组等于Active。

$\mathsf{OpFrame}(p)$ 包含父运行heap、control、heads、registers、latches、当前权限、
普通连接及其partial状态和owed action。
公共journal／inventory／累计费用、retired child档案与生命周期selector元数据、
专属wake控制及backing不在这个frame中，仍全部在 $X_r$ 内。
“返回原活动”只要求这个frame及其owed action恢复，不要求全局状态回滚。

**假设 60.4（六组实际前提）。** 以下各项同时保持。

- H-G：$G$ 是自身真实不可约入口 $z_0$ 的完整有限描述；source模型穷尽实际写者与状态。
  覆盖期内没有未建模clock、DMA、熵、竞争写者、撤权、崩溃或耗尽。
- H-R：缩减记录给真实actor、实际总顺序、literal前态规则tag、规定外来输入及真实birth绑定；
  固定不可变coeffect忠实执行。它不提供被删除的确定性效果endpoint。
- H-234：AS50.3–50.5的全参与者门控、独立进入、held控制／head／register及端点权限、
  冻结inventory读取与个别操作、custodian独占线性释放均实际委托，原source权限及声明的原子粒度保持。
- H-W：对每个covered cut、每个有限森林的每个node，均有当前source-bound wake授权、
  指定peer的一次genuine one-bit handoff、真实origin与有限材料。
  它不依赖原input／ACK、父pool、父完成或ancestor协议。
- H-F：保留AS26.2的逐点有限材料、合法原ingress／ACK、已到达的prior／controller终止；
  每个请求另有合法有限framing、四次delivery、选择、完整selected return、规定genuine ACK和本地进展。
  在有限干扰耗尽后给原进展；producer执行下述算法，traffic不直接提供目标答案。
- H-E：固定同一组非负原与新增tariff，全部真实操作、reference-bit访问、grant与材料按互斥归属收费；
  删除披露不删除被披露的private工作。

H-W供应真正offer与权限；第63节证明的是所装源的ready性质，不把ready当作offer。
上述权限、原子性和实际供应是前提，费用不能替代它们。

**定理 60.5（完整域的缩减记录取得与返回）。** 在假设60.4下，同一个有限 $J_r$ 安装覆盖定义60.2全域。
每个请求的四个独立实际received body各自解码为同一 $X_r(H)$；
完整所选实收body经过独立解码和当前真实身份解析，供应逐项控制回写及一次线性释放的实际操作数。
每个有限请求森林有限完成，并把同一个父活动接回同一个owed action；
原输入缺失时仍pending，有原输入及进展时恰执行一次。
原ordinary、准确mode10、全部原projection与terminal消费者保留，
所有新旧工作在同一次实际历史上满足第73–74节的精确费用与同时peak。

证明分解如下：第61–65节给缩减源对应及完整重建；
第66节证明立即嵌套的null入口与保持不变量；
第67–69节给四份结构、真实复制和实收消费；
第70节将它们闭合于全部partial cuts和有限森林；
第71–72节建立原source投影并接回全部原消费者；
第73–74节逐项给同次账。各步只用前述真实供应，不先执行父owed action。
将这些结论依次组合即得本定理。$\square$

## 61. 真实入口、缩减披露与自登记日志

**定义 61.1（入口及允许观察）。** $G$ 精确描述 $z_0$ 实有的有限typed材料、常量和基础授权：
原primitive meter／control、有限bootstrap／gate、基本Active、空journal／inventory根、
primitive wake根及其真正已有的基础binding／grant。
此时 $L=\mathsf{null}$，无journal node，原meter零receipt。
未知seed／code／input、saved client、安装程序、四根及操作records不是免费已知snapshot；
它们在后续实际构造、输入、初始化行中进入历史。
未记录的过去不能通过宣称“genesis”补入。

删除的披露包括Native与AA的确定性RD／READ／BF／test结果、
求值后的地址／写值、branch／next-PC／poststate及effect callbacks；
删除范围包括所有channel参与者、allocator、wake、support与evaluator。
不保留shadow mirror、live private-heap reader、snapshot、隐藏invoice、延迟效果结果，
也不借F3行政endpoint作为replay的实时读取后门。
F3只在真正返回时使用当前held-binding与授权，不供应重建缺失结果。

**定义 61.2（封闭缩减tuple）。** 每个真实联合occurrence的允许记录为

$$
\rho=(a,q,u,\beta,j).
\tag{AS61.1}
$$

$a$ 为真实actor；顺序是实际前驱顺序。
$q$ 来自固定有限literal前态规则表，含真正boot变体；
它不能编码动态地址、数值、branch结果、深度、对象tag或private结果。
$u$ 只有以下三类：

$$
\mathsf{None},\quad
\mathsf{ExternalIngress}(b,o),\quad
\mathsf{AuthorizedWake}(w,1,o).
\tag{AS61.2}
$$

外来word须由实际逐bit事件进入；内部OUT、内部ACK和确定性branch不是新外来选择。
origin只表示真实有限provenance，不暗藏parent状态、费用或授权。
$\beta$ 只列该规则规定的真正fresh对象、endpoint、原receipt及backing等birth槽；
不得用dummy birth传结果。每行槽数有固定界，实际reference宽度无统一常数。
$j$ 是这一次真实fresh journal节点绑定，不用相等payload的另一个节点代替。
外来bit、origin与birth是剩余外参；其余效果必须由前态和源律求出。

**定义 61.3（单次固定自登记coeffect）。** 联合occurrence依次执行core、
适用时原Native receipt，再执行一次固定有界缩减journal／inventory coeffect。
若旧tail为 $l$，以真实 $j$ 写

$$
j.\mathsf{prev}=l,\qquad
j.\mathsf{payload}=(a,q,u,\beta),\qquad L=j,
\tag{AS61.3}
$$

并安装固定immutable read／retention grants。
所有实际birth、endpoint及其type／group／grant描述都登记，
包括未链接、未初始化、Reserve和status0对象。

登记段使用固定schema和真正fresh槽；它同时登记core births、$j$、自己的段binding及规定backing。
段内可有指向自身真实binding的固定引用，描述元数仍有界；
写者按这一模板一次完成，不因“段也须被登记”再启动logger。
其节点、字段、grant、reference backing和tail写全部是真实材料及收费效果。
自引用登记不改变journal的严格旧prev关系。
core及这些coeffect同属一个原子occurrence；普通日志读取／复制仍各为可请求的软件步。

custodian具有每个闭合prefix的真实read／retention权。
目标capsule固定 $c.\mathsf{cut}=L(H)$ 及 $H$ 的inventory端点；
之后的节点和bindings不延长这次扫描的输入。
当前child及key在目标之后出生，由当前实际custodian binding另行取得，不伪造在旧inventory中。

**定理 61.4（缩减接口没有结果通道）。** 在定义61.2–61.3下，
一次记录只额外引入规定外来输入和实际birth身份；journal／inventory自登记不会重新引入确定性private结果。

证明。$q$ 在调用前固定，故不能随结果改变。
$u$ 的三个构造子分别无输入、真实外界单bit及真实wake，均无任意结果槽。
$\beta$ 的位置由规则固定且必须是实际birth，不能以出生个数或伪对象编码结果。
真实 $j$ 和登记段的字段仅是旧 $L$、这些允许参数及固定类型／grant模板的函数。
逐个代入模板可确定所有登记引用，无一步读取core的private结果。
元数有界只约束槽数；实际identity／origin表示仍需完整保存和付费。
所以返回的typed binding说明真实分配，不构成结果或新授权。
被删去的效果若要出现在四表达中，只能由第64–65节的源对应重建。$\square$

## 62. 独立唤醒插座的具体安装与授权

**定义 62.1（所装有限源）。** 固定一个source-bound同步wake插座 $W$，
其真正sender endpoint为 $w$，custodian为 $a_W$。
所有获准requester通过这个绑定peer供应自己的genuine wake；不按深度设端点。
$W$ 的root在enable后不可变，实际槽为

$$
(\mathsf{sender}=s,\mathsf{connection}=v,\mathsf{receiver}=r,\mathsf{backing}=d,
 \mathsf{peer}=w,\mathsf{custodian}=a_W),
\tag{AS62.1}
$$

并持实际EnableCapture／ENTER／selector bindings。
四个操作record互不别名，也不别名任何原或ancestor的协议session／ACK／input／工作池。

| record | 全部可变字段与域 |
| --- | --- |
| $s$ | $\mathsf{pc}\in\{\mathsf{Ready},\mathsf{Offered}\}$，$\mathsf{pendingBit}\in\{\mathsf{empty},0,1\}$，$\mathsf{pendingOrigin}\in\mathsf{Origin}\cup\{\mathsf{null}\}$ |
| $v$ | $\mathsf{full}\in\{0,1\}$，$\mathsf{bit}\in\{\mathsf{empty},0,1\}$，$\mathsf{origin}\in\mathsf{Origin}\cup\{\mathsf{null}\}$ |
| $r$ | $\mathsf{pc}\in\{\mathsf{Listen},\mathsf{Latched},\mathsf{Backed}\}$，$\mathsf{bit}\in\{\mathsf{empty},0,1\}$，$\mathsf{origin}\in\mathsf{Origin}\cup\{\mathsf{null}\}$ |
| $d$ | $\mathsf{valid}\in\{0,1\}$，$\mathsf{bit}\in\{\mathsf{empty},0,1\}$，$\mathsf{origin}\in\mathsf{Origin}\cup\{\mathsf{null}\}$ |

origin是实际允许的provenance atom，带其真实有限表示与所需backing，
不是任意word或执行endpoint。$d$ 只存最近一次wake backing，不存ancestor副本。
以上穷尽wake可变状态；没有隐藏counter、quota、random、queue、ACK、延迟cleanup或别处的sender状态。
不可变type／source／endpoint incidences属于真实allocation header。

**定义 62.2（付费安装与grant分工）。** primitive根及基础委托只有确在 $G$ 中的部分属于入口。
$s,v,r,d$ 经四次真实固定schema allocation取得binding、初始化／保留端点，初始数据字段未初始化。
以实际返回写root链接、source／sender／custodian绑定，再逐项作十二次数据初始化写：

$$
s=(\mathsf{Ready},\mathsf{empty},\mathsf{null}),\quad
v=(0,\mathsf{empty},\mathsf{null}),\quad
r=(\mathsf{Listen},\mathsf{empty},\mathsf{null}),\quad
d=(0,\mathsf{empty},\mathsf{null}).
\tag{AS62.2}
$$

类型、grant表、端点、root引用、backing、有限source规则／control／code及enable检查／写
均由实际postentry行构造并缩减记录、收费。早先未写字段仍未初始化。
有限表先构造，外部description及identity后构造，再绑定真正返回端点；
固定规则只访问typed槽，不含未来 $c,k$、深度或input流的literal。

安装者只有真正委托的ALLOC／initialize／bind权。
EnableCapture关闭这些已装link及四record的普通可变访问。
之后 $w$ 只能提供source-bound genuine one-bit rendezvous，
不能设置parent PC、直接写 $d$ 或选择private结果；
$a_W$ 持执行第63节compound rendezvous及capsule／key／selector的当前权。
普通active组与sampler无 $s,v,r,d$ 的live private读写；
固定源律内部通过已装binding访问它们。

后代allocation按H-234已委托的generic模板返回capsule操作端点，
custodian保留held-context行政端点和唯一key生命周期权。
$\beta$ 记录真实返回，真正allocator执行grant；identity字不产生grant。
journal／inventory只给规定immutable read／retention端点。
handoff不修改 $W$ 的任何grant或不可变link，所有grant表示与扩展材料按真实birth计费。

**定义 62.3（无祖先条件的ready不变量）。** 令

$$
I_W:\quad
s=(\mathsf{Ready},\mathsf{empty},\mathsf{null}),\
v=(0,\mathsf{empty},\mathsf{null}),\
r=(\mathsf{Listen},\mathsf{empty},\mathsf{null}).
\tag{AS62.3}
$$

$d$ 为初始三元组或最近一次完成handoff的backing。
$I_W$ 对Active、localRoot、原input、token分布和其他连接均无条件。
缺offer不是一次ENTER、receipt或source refusal；
真正执行的普通授权测试另记其自己的行。
这一区分保持全部cut域，而不以“已有wake位”重新筛选域。

## 63. 同步唤醒的逐赋值源律与对应证明

**定义 63.1（一个原子ENTER的完整足迹）。** 在covered cut，读旧
$p=\mathsf{Active}$、$l=L$。
自动gate检查enabled／prehalt、当前custodian ENTER／selector权、
source-bound $w$ handoff权及真正 $\mathsf{AuthorizedWake}(w,1,o)$。
source core以九次字段读／测试检查式(AS62.3)的九个phase／empty／null条件。
供给真实fresh $c,k$、其模板要求的endpoint及规定journal／inventory／backing槽；
没有新wake-control对象，也没有原Native receipt槽。

同步sender offer、接收、backing、重新开放全在这个保留的有限原子ENTER内。
按下列顺序执行二十二次赋值，分组不增加外部cut：

$$
\begin{aligned}
\text{W1:}\quad&
 s.\mathsf{pendingBit}:=1;\quad s.\mathsf{pendingOrigin}:=o;\quad s.\mathsf{pc}:=\mathsf{Offered};\\
\text{W2:}\quad&
 v.\mathsf{bit}:=s.\mathsf{pendingBit};\quad v.\mathsf{origin}:=s.\mathsf{pendingOrigin};\quad v.\mathsf{full}:=1;\\
\text{W3:}\quad&
 r.\mathsf{bit}:=v.\mathsf{bit};\quad r.\mathsf{origin}:=v.\mathsf{origin};\quad r.\mathsf{pc}:=\mathsf{Latched};\\
\text{W4:}\quad&
 d.\mathsf{bit}:=r.\mathsf{bit};\quad d.\mathsf{origin}:=r.\mathsf{origin};\\
&d.\mathsf{valid}:=1;\quad r.\mathsf{pc}:=\mathsf{Backed};\\
\text{W5:}\quad&
 v.\mathsf{full}:=0;\quad v.\mathsf{bit}:=\mathsf{empty};\quad v.\mathsf{origin}:=\mathsf{null};\\
&r.\mathsf{bit}:=\mathsf{empty};\quad r.\mathsf{origin}:=\mathsf{null};\quad r.\mathsf{pc}:=\mathsf{Listen};\\
&s.\mathsf{pendingBit}:=\mathsf{empty};\quad s.\mathsf{pendingOrigin}:=\mathsf{null};\quad s.\mathsf{pc}:=\mathsf{Ready}.
\end{aligned}
\tag{AS63.W}
$$

W2、W3、W4各有两次明确value读取，共六次；
二十二次写中有七次origin-reference写、十五次有限symbol／bit／phase／flag写。
实际link解引用另列，不能藏在这六次value读数内。
W4覆盖此前真实 $d$，不假设它空；此前效果仍在历史中。

然后以真正 $c,k$ 初始化十八个capsule数据字段：

$$
\begin{gathered}
c.\mathsf{parent}=p,\quad c.\mathsf{cut}=l,\quad c.\mathsf{peer}=w,\quad
c.\mathsf{key}=k,\quad c.\mathsf{localRoot}=\mathsf{null},\\
c.\mathsf{pc}=\mathsf{Entry},\quad c.r_1=\cdots=c.r_4=\mathsf{null},\quad
c.\ell_1=\cdots=c.\ell_8=0,
\end{gathered}
\tag{AS63.1}
$$

并写 $k.\mathsf{child}=c,\ k.\mathsf{parent}=p,\ k.\mathsf{unspent}=1$。
真实allocation header给 $\mathsf{type}(c)=\mathsf{Capsule}$、$\mathsf{group}(c)=c$、
$\mathsf{retired}(c)=0$、$\mathsf{type}(k)=\mathsf{Key}$及custodian生命周期ownership，
按固定模板给endpoint／group／grant，最后 $\mathsf{Active}:=c$。
不增加capsule可变数据字段，不改任何旧操作frame。
$c.\mathsf{peer}=w$ 不把稍后新建的capsule session认同为这四个wake records。

最后施行定义61.3的一个缩减coeffect：

$$
j.\mathsf{prev}=l,\quad
j.\mathsf{payload}=(a_W,\mathsf{ENTER},\mathsf{AuthorizedWake}(w,1,o),\beta),\quad L=j.
\tag{AS63.2}
$$

登记真实新bindings及模板grants，$c.\mathsf{cut}$ 仍为 $l$。
没有另一次wake事件、未列ACK、额外写或暗藏grant变化。
先前别处真正发生的发送／准备／backing仍各在ENTER前prefix，不因同步源律被删去。

**定理 63.2（每个covered边界的wake就绪）。** 安装后每个covered边界满足 $I_W$；
$d$ 恰为初始值或最近一次真正handoff的 $(1,1,o)$。
因此任何Active，包括null localRoot的Entry，均无须父进展即可接受H-W供应的下一wake。

证明。十二次安装写建立式(AS62.2)，EnableCapture只在它们及真实授权完成后发生。
普通原／支持／LEAVE／journal行无权写四records，故保持九个ready字段。
ENTER的W1置真实 $1,o$；代入W2的两次读取得 $v=(1,1,o)$；
再代入W3得receiver持同一个bit和origin，连接到W4之后才开放。
W4先将 $d$ 写成 $(1,1,o)$ 并进入Backed。
W5的九次固定写逐项恢复式(AS62.3)，不读parent或等待ACK。
按联合occurrence数归纳即得所有边界。
这里没有普通cleanup前的漏掉cut：W1–W5是本源明确保留的原子足迹，
其软件细分若成为另一个source，须另证其新cuts。
ready不产生真实offer，最后一步可执行仍用H-W。$\square$

**定理 63.3（缩减ENTER的显式交换步）。** 若重建前态 $M$ 与实际前态 $z$ 按真实名字完全相等，
且给同一个允许缩减项，则仅用该项和定义63.1可求出ENTER全部实际读／写／控制／backing、
birth／grant／journal效果及其tariff参数。

证明。相等前态给同一个 $W,s,v,r,d,w,a_W$ binding、九个ready字段、当前rights及旧 $p,l$。
$q$ 指向的正是定义63.1；$u$ 只给真实 $w,1,o$，$\beta,j$ 只给真正fresh槽。
W1在同一个 $s$ 写相同外参。
W2的两次读取在两边都读到刚写的 $1,o$，故实际读terminal、目标 $v$ 及三个写值相同。
W3同理由同一个 $v$ 读 $1,o$，W4由同一个 $r$ 读 $1,o$，
且两边覆盖的是同一个旧 $d$ 及旧值；W5再作同序同值的九次写。
这逐项确定全部六次value读取、二十二次写及其内部版本，
包括数值未改变的实际写，而非仅证明最终ready相同。

旧 $p,l$ 与真实fresh $c,k$ 决定式(AS63.1)、三项key数据及其alias。
固定allocation／grant模板决定header和权限描述；真实活权本身由H-234供应。
真实 $j$ 和旧 $l$ 再代入式(AS63.2)及固定登记模板，
给同一个birth集、inventory、retention及tail。
未列字段按源律不写，故两边完整后态相等。
每个access的操作数、reference宽度、新材料及顺序内前态也由上述逐项代入确定，
故实际tariff参数相同。
这个证明不使用被删除的sender结果endpoint、live F3读取或generic“系统确定性”作为缺失步骤。$\square$

**定义 63.4（literal唤醒发票）。** 令 $\mathcal A_{\rm ENTER}$ 为定义63.1真实有序访问／分配表，
包含九次source-body测试、六次value读、二十二次写、实际W-link解引用、
旧Active／L读取、$c,k$及endpoint出生、header／grant、十八加三项数据初始化及selector写；
也包含真实handoff、origin／reference表示与新增材料。
以每项自己的实际顺序内前态 $z_a$ 定义

$$
\delta_{\rm core}(\mathsf{ENTER},z)
 = e_{\rm enter}+\sum_{a\in\mathcal A_{\rm ENTER}}\mathsf{tariff}(a,z_a).
\tag{AS63.3}
$$

$e_{\rm enter}$ 只记ENTER基础计数，排除已在和中收费的访问／材料。
自动权限gate和一个缩减journal另计，角色不重复。
ENTER不是二十二或二十八个日志事件；这些是一个原子联合occurrence的内部收费访问。
其中无原Native core，所以原Native receipt／tick／fee增量均为零。
第63.3定理给每个 $z_a$ 的实际对应，包括覆盖旧backing的费用，而不从origin读取隐藏bill。

## 64. 其余有限源规则的逐类效果对应

**定理 64.1（有限source-row对应）。** 对 $J_r$ 的任意实际下一联合occurrence，
若所表示前态等于真实前态，给同一个定义61.2缩减项，
则可由固定有限规则求得全部实际effects、birth、权限描述、coeffects及收费前态；
不需任何被删去的private披露。
这种求值只作用于重建数据，不推进live源。

证明。先确定规则并集的来源：Native部分用AS1.2–1.4与
[TMC PR57.D1及(PR57.03)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)；
AA部分用[AA17.1、20.1–20.3、22.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)。
固定slot／field selector来自literal行或已重建的code／register，
而不是结果披露。逐类检查如下。

**Native读取、写入与移动。**
RD由真实port binding及head mark选中已存在的cell，
读该cell的实际已初始化symbol进指定latch；测试行按literal immediate作比较，
依(PR57.03)的两个有限后继取其一，非测试行两个后继相同。
两边head、symbol、immediate相同，故read terminal、latch、后继逐项相同；不隐藏seek或填补未初始化值。
WR由当前可写head、literal symbol或已有latched bit确定目标和值；
即使旧值相同也产生一次写及相应版本。
ML／MR沿实际constructed adjacency，检验真实L／R边界，
修改原head cell与相邻cell的两个mark。邻接和guard已在前态，故两边一致；
越界disabled不变成一次成功移动。

EX在真实旧R处，将这个cell变为blank，取规定birth槽的真正新R，
把它接在旧R右侧，head留在旧R现已变blank的cell，
按原规则初始化新mark。并非把head移到新R或预造一段tape。
boundary-constructor与bit-install boot变体同理由其literal规则、真正birth或外来bit逐项确定。
原meter extension由下段的独立固定receipt coeffect处理。

**Native布尔、I/O与token。**
BF读latch0–2的实际operand-bit子字段，按指定八bit truth table给latch3；
table code已由早先实际输入／读取进入前态，不是新的外来结果。
IN对内部连接使用已表示的真实bit、origin、endpoint与receiver phase；
只有真正外界边界取 $u=\mathsf{ExternalIngress}(b,o)$。
该行把bit放入指定input latch并取literal后继，不顺便WR、移动head或开放下一位。
OUT使用实际output latch、route、sender binding、empty条件及sender phase，
由原channel规则得真实bit／origin及sender／connection变化。
内部确定性发送不转记外来选择；此前OUT即使尚未被IN消费仍留在历史中。

TOK只按literal guard转移指定真实token的owner／availability。
十二TOK的每个中间分裂分别保留，第一TOK之后不会推断完整Init或使helper提前可用。
16／17／25／27／74从来不进入工作池。
前态owner相同给相同转移；不存在将部分loan归并成一次整体借还的步骤。

**Native控制与旧receipt。**
CTL检验实际finite latch、phase、role、seal、commit、fence等字段，
按已安装的finite row取后继。
真正Y来自之前实际parser／MUX／STORE／source行，不是 $q$ 附带的answer。
executed refusal、strict／unchanged／maintenance-refusal、controller domain exit、
BadFrame／FaultHeld、disabled none、partial status0、halt各按原标签分别处理。
halt是吸收态，禁用后续ENTER及支持执行。

每个真正原Native core后，旧meter append-R成为普通receipt或该CTL指定的fence，
真正新R按规定birth接上并设置append mark。
read cursor保持原receipt规则规定的实际mark关系，不因“读取日志”跳到虚构尾端；
若同一个旧cell带read mark，其保留由这个cell的真实字段决定。
两边旧meter、fence控制及真正birth相同，故coeffect逐字段相同，
恰增一receipt、一tick、二fee。
没有另一个private值transcript；AA和新增支持行不冒记Native occurrence。

**AA分配与grant。**
真实allocator返回的object、endpoint及规定backing从固定birth槽取。
固定模板写type、group、ownership与其真正初始化字段，
执行实际初始化／retention／操作grant；其余字段仍未初始化。
reserved、unlinked、status0对象已是实际birth，立即登记inventory，
不等root可达或Ready。相同名字的两个真正birth不合并。
权限描述由模板可求；活的权是H-234的实际allocator结果，不由描述字自行生成。

**AA个别字段、引用与测试。**
READ／WRITE／reference-copy以实际reference register或slot及固定field selector选对象。
前态相等保证null、alias、旧值和目标顺序相同，因而每个read terminal及write相同。
未定义或disabled的未初始化读取不能以零替代；
程序先测试初始化，或严格按其literal已声明行为执行。
null／reference／bit／symbol／phase／right测试也在表示前态上逐字段比较，
给同一个finite后继。缺right、错phase的disabled原语与实际source refusal是不同情形。

**普通channel的全部参与者。**
每个sender、receiver、queue、local ACK和backing控制器按自己的真实字段求值，
保留OUT-empty、IN occupied latch、backing-before-reopen、
实际origin／方向／stage和每个cursor。
外来ACK只有在真正外界输入边界才用 $u$；内部ACK由前态得出。
接收bit不会抹去先前sender的实际效果，也不能在backing前提前开放连接。
独立W的sender不在此抽象化：它已由第63.3定理逐赋值处理。

**AA源程序及原消费者。**
Navigate／Guard／Reserve／edit／Maintain／Build／ReadBody／supervisor
是前述allocation、field、reference、bit、test、control行的程序。
真正P／S、source／parent binding、祖先child-reference比较、side／next初始化、
head或next链接先于tail-last写均由各自前态决定。
故source已complete而Maintain未complete的对象仍为partial。
例如first-$P_R$在head已链接而tail仍null处，
下一literal行是tail写；执行后前态给不同tail与AA收费，
不能用相同Native stamp把两处合并。
INPUT的固定尾和STACK的增长尾是两个reference，不作一个共同循环终点。
packet、settlement、terminal等程序也逐行使用同一个finite引擎，
没有名为“整个consumer”的原子求值步骤。

**历史resolver与行政写。**
历史inventory扫描的cursor、entry、identity-bit比较及匹配结果均取表示中的实际工作字段；
当时的WRITE目标和值来自当时已经收到并解码的register。
故重建该历史WRITE只需重建其过去的个别行。
真正当前返回的binding取得及授权检查另在第69节执行，
不能把历史rights数据cast成活endpoint，也不能使用免费Resolve或bulk restore。

**ENTER、LEAVE与固定登记。**
ENTER用第63.3定理，包含旧backing及完整有序访问。
LEAVE由真实custodian权、Active、key.child／parent／unspent、
已收到并解析的parent操作数作top／parent／unspent检查；
在同一原子边置unspent为0、child retired为1、Active为parent。
不动W，不执行父动作，不重置ancestor key。
完整body验证和回写都在它前面的付费软件行，不在LEAVE里塞入判等oracle。
最后，所有行都以真实 $j$、旧L及允许payload代入定义61.3固定模板，
得同一个journal／inventory／grant／tail效果，无第二层logger。

**evaluator自身及穷尽性。**
map、counter、stack、effect／graph builder、codec、parser、比较及restorer
都由上述field／bit／control／allocation行组成。
过去某evaluator的下一步只读取其当时实际reference register所指工作对象，
不调用它未来将算出的完整答案。
AS1.4固定Native／AA literal opcode与slot词汇，TMC给finite transition及finite-control展开，
AA20／22展开源程序；新增软件用同一字段引擎，
仅额外保留明列的ENTER／LEAVE及receipt／journal原子项。
W安装是普通allocation／field／control行，其后只有第63节源律。
所以每个实际occurrence均在这个有限并集中。
任意长数据、循环次数和森林高度只增实例数，不增加规则种类。
以上逐类已证每项效果相等，连同固定coeffects即证完整对应。
这一穷尽性是源schema的证明，不是有限样例外推。$\square$

## 65. 有价literal求值与自身日志的时间闭合

**定义 65.1（实际求值程序）。** $\mathsf{Eval}$ 是一个有限字段机程序，输入仅为真实 $G$
及冻结缩减链 $R(H)$。它不用live源heap，也不取得private结果。
其实际操作分为以下有限循环。

先沿固定 $c.\mathsf{cut}$ 的prev到null，逐项收集真实node及允许payload，
压入自己的实际stack，再反转得到正序。
复制 $G$ 时保留type、未初始化／null、真实identity及alias，
在新workspace分配表示节点；表示节点的本地binding与它表示的历史实际identity分开。
map用真实有限表，lookup作完整identity-bit扫描与比较；
整数、字符串、counter与stack均由实际field／bit行处理，没有原子map或arithmetic。

每项先全解析actor／literal $q$／白名单 $u$／birth槽／node及prev，
查真实有限schema和当前模拟code／register；
按第64.1定理执行一个历史source行，
由前态算出所有read／write／test／control／I/O terminals。
适用时展开原receipt，再展开一次固定缩减journal／inventory模板。
写入新的表示字段、版本、rights描述、retained材料表和真实前态tariff累计表。
完成末项后给式(AS60.2)的完整表示。
原始birth identity始终作为历史名字保存，不能用workspace allocation替换它。

每次lookup固定本次查找时表的既有范围；
collector固定旧cut，resolver固定H-inventory，
parser固定完整received INPUT的length／ending，另设可变STACK；
graph、version、event及wire构造各消费已经确定的有限对象集合。
工作扩展写到自己的输出表，不把正在增长的全局L或STACK当作输入终点。
所有中间cursor、partial record、counter与未seal结果都在raw heap中。

**定理 65.2（literal求值的逐点终止）。** 对任意真实有限 $H$，
在H-F材料及本地进展下，定义65.1有限完成；自身生成的后续日志不引起追尾或自解释回归。

证明。设旧prev链长 $m$。每个prev严格指向实际较早节点，
$L=\mathsf{null}$ 为唯一入口，故收集恰 $m$ 次并结束；反转消耗固定stack。
$G$ 有限，完整复制有限。
对前 $i$ 项归纳，表示对象表、字符串、rights与材料表均有限；
第 $i+1$ 项的规则访问槽数有固定界，每次slot解析仅扫描当时固定的有限表、
比较有限identity并作有限field／bit行。
该行新增有限记录及实际有限reference backing，故处理有限且保持表有限。
原receipt及新journal模板也只增有限槽，归纳至 $m$ 即止。
完整历史／费用输出由这些有限表作有限扫描。

每个求值软件行确实生成自己的新journal节点，但它在旧cut之后，
不在正在消费的prev链中，所以不能增加 $m$。
若旧 $H$ 本身包含较早evaluator，它的一次历史动作只是某个已发生的field行：
此行的工作register、map和code都在当时前态中，
本次模拟它不要求先证明或调用该旧evaluator后来的完整成功。
归纳按真实occurrence索引严格前行，不沿“解释器解释自己”倒向未来。
新生成的日志等将来的请求再以同样方式处理。
故没有无限logger、免费递归Eval或等待未来源完成。$\square$

**定理 65.3（真实名字下的完整重建）。** 对从真实 $G$ 开始的每个实际有限联合prefix，
包括boot／安装、原与支持任意partial阶段，

$$
\mathsf{Eval}(G,R(H))=X_r(H).
\tag{AS65.1}
$$

等号是实际名字、alias、raw字段及来源均相等，不是重命名同构。
它恢复rights与费用的数据；执行动作仍要当前真实授权。

证明。对occurrence数 $m$ 归纳。
$m=0$ 时 $G$ 正是 $z_0$，L为null、原receipt为零，
$H$ 为空，$C=C_{\rm gen}$，retained材料恰为入口实际材料；
未知seed／code和未来输入均未出现。定义65.1逐tag复制给同一个基态。

设前 $m$ 项已经完全相等。
下一缩减项给真实actor、prestate rule、允许外来bit／wake及真实birth。
第64.1定理和第63.3定理给该实际core的每个read、写位置／值、test、
控制、origin、同值写、refusal、birth与权限描述；
未初始化及尚未发生的seal保持原样。
原Native时附的receipt也相等。
继以真实 $j$ 展开固定coeffect，旧L、prev、登记段自引用、
全部typed binding、read／retention grant及新tail相等。
因而整个联合后态和完整occurrence相等，原alias也没有被workspace身份取代。

第73节的材料birth互斥分区与core／gate／journal访问角色
在这个已知前态、必要时内部顺序前态中逐项确定；
第63.3定理特别给ENTER覆盖旧backing等所有tariff参数。
故同一个 $\delta$ 加在同一个累计值上，得相同 $C$；
实际birth／extension／保留／release给相同 $\mathsf{Ret}$。
这证明 $X_r$ 的全部分量相等。
第65.2定理保证实现这些有限归纳步骤的实际程序完成；
其live新日志在目标之后，不改变被证目标。$\square$

**定理 65.4（同缩减记录的源内充分性）。** 同一真实入口、安装、源schema及tariff参数下，
两条真实历史若具有完全相同的 $G,R$，则其 $X_r$ 相同。

证明。对各自真实历史应用式(AS65.1)，两边均等于同一个有限求值结果。
这里只比较该具体源内的真实image；
换source、漏掉入口、改grant或遗漏外来输入，均不满足前提。$\square$

## 66. 紧接ENTER的null子请求与操作框架保持

**定理 66.1（首个parent动作之前的再进入）。** 任意covered前缀 $H_0$，
设旧Active为 $p$、旧tail为 $l_0$。
第一真实wake origin为 $o_1$，ENTER产生 $c_1,k_1,j_1$。
即使第一支持活动尚未执行一个普通动作，
第二个H-W供应的wake $o_2$ 也能产生 $c_2,k_2,j_2$。
第二请求完整目标是 $H_1=H_0;\mathsf{ENTER}_1$，
不会漏掉第一次实际sender／backing／费用，也不会把第二次效果塞进自己的旧目标。

证明。第一ENTER后按第63节，

$$
\begin{gathered}
\mathsf{Active}=c_1,\quad L=j_1,\quad
c_1.\mathsf{cut}=l_0,\quad c_1.\mathsf{localRoot}=\mathsf{null},\quad
c_1.\mathsf{pc}=\mathsf{Entry},\\
k_1.\mathsf{unspent}=1,\qquad d=(1,1,o_1).
\end{gathered}
\tag{AS66.1}
$$

$I_W$ 已恢复；其条件没有localRoot，因此H-W真实第二handoff可立即发生。
第二ENTER使 $c_2.\mathsf{parent}=c_1$、$c_2.\mathsf{cut}=j_1$、
Active为 $c_2$、L为 $j_2$，live $d=(1,1,o_2)$。
沿 $c_2.\mathsf{cut}$ 求值恰消费至 $j_1$。
其中第一次缩减ENTER项由第63.3定理恢复完整W1–W5、
$c_1,k_1$、旧selector、coeffect及真实费用。
所以第二请求的四表达均恢复 $X_r(H_1)$：
历史 $d=(1,1,o_1)$、parent为null-root Entry，且没有第二ENTER。

完整selected return从实收解码取得 $c_1$ 身份及其Entry／null控制。
$c_1$ 已在 $H_1$ 真正出生，冻结inventory可返回它的实际binding；
$k_2$ 则从当前custodian实际binding取得，不在旧目标中捏造。
null字段回写的是literal null，不是强求一个完成localRoot。
第69节的个别回写及 $\mathsf{LEAVE}(k_2,c_1)$
spend $k_2$、retire $c_2$并选回 $c_1$，
$k_1$ 仍unspent，$c_1$ 首个Entry动作仍未发生。
尤其不把历史 $o_1$ 写回live $d$：第二handoff及后续全局日志、材料、账继续保留。
$c_1$ 自己的目标仍是 $H_0$／$l_0$。$\square$

**定理 66.2（统一held-frame不变量）。** ENTER从 $p$ 选到 $c$ 后，
直到匹配LEAVE，$p$ 及其ancestor操作frame、原权限及owed action保持；
算法允许的个别行政回写与进入值相等。
公共journal／inventory／wake／archives／费用可真实改变。
不变量对PC、栈高、seal、pool完整性或localRoot非null均无前提。

证明。ENTER足迹只有独立 $W$、fresh capsule／key／headers／grants、selector及固定coeffect，
不触及父操作frame。wake sender与祖先普通session分离是这里必用的实际不别名条件。
选择child后，所有ancestor的普通invocation组不同于Active，
因此原driver、sender、queue、receiver及backing都不能自行推进。
只停receiver不足以得到这个结论；此处用H-234对全参与者的门。
child普通工作只改自己的session／workspace及公共追加状态，不借父pool／scratch。

剩下可能写父frame的只有指定行政返回循环。
可对真实步骤同时保持以下断言：每个held frame等于其进入值；
每个已完成的行政写取自该次完整实收解码，值等于相应进入值。
第65.3定理对每个真实prefix独立成立，不假定任何parent已完成；
第67–69节的完整复制与检查保证该decoded值确为该进入cut。
因此一次行政写只把某字段写成其已有值，保持断言。
处理完的字段、未处理的字段和其他held heap均保持，
这一逐步断言无需把whole restore设成原子。

再次ENTER把当时Active的全部partial运行heap留在原处，
同一门控证明对它成立；其已完成的若干行政写也已经是同值写。
child返回只花自己top key，不能普通WRITE重置或消费ancestor key。
LEAVE原子spend／retire／select且不执行父动作，
故归纳经过每个实际步骤一直保持断言。
返回正确性的复制、解码部分只依赖真实日志与不可变输入，
本不变量只为回写前后的live frame判等，二者没有以未来父完成互作前提。
公共域从来没有被断言不变，所以live $d$、费用及子档案的增长不构成反例。$\square$

## 67. 同一目标的四种实际结构及逐体逆

**定义 67.1（共同codec与来源头）。** 每个body有完整有限头：
kind、真实source／genesis／install／schema、冻结cut binding、切口Active parent。
自然数用 $U(n)=1^n0$，有限bit字用 $B(w)=U(|w|)w$；
有限list先写长度，再写各项，固定tuple按schema次序写。
type、field、initialized／uninitialized、null／reference及finite symbol各有不混淆tag。
identity写其完整实际有限表示；相同引用重复相同名字，两个birth不因payload相等而合并。
length和identity取得仍是付费逐bit遍历，不设length oracle。
逆必须消费全部length／body／ending并检查exhaustion。

下述结构均关于同一个 $H$ 的实际image，完整信息由第65节从 $G,R(H)$ 求得；
它们不改用另一个具有相等答案的源。

**定义 67.2（时间体 $\mathsf T_r(H)$）。** 时间体是完整有序联合occurrence／effect序列，
每项包括实际actor、literal规则、允许外参、真实birth／$j$／prev，
以及由对应求出的每个read、write、test、control、I/O／origin、
原receipt、自动gate及固定journal／inventory effects。
同值写、执行过的失败测试／refusal都列出；disabled none不是假造事件。
ENTER在一个原子event中保留九个body测试、六个value读、
二十二次按序wake写、capsule／key及coeffect的内部terminals。

其逆先取所列 $G$ 与缩减项，再按第65节求值，
逐个比较body所列全部effect terminals、birth、coeffect、前后状态及费用参数。
检查成功才返回完整 $X_r$，不是仅取最后tree或terminal答案。

**定义 67.3（空间体 $\mathsf S_r(H)$）。** 空间体为有限typed incidence graph。
实际object／cell／endpoint各有一个identity顶点，实际occurrence各有一个event顶点；
event另有实际总前驱spine，不以图的任意topological sort替代实际交错。
关联边标birth、read、write、test、control、grant、root、parent、header、
tape邻接／mark、channel、origin及binding。
每个field版本以 $(\text{event},\text{内部access次序})$ 标识，另有genesis版本；
read连当时版本，write连旧／新版本，即使值未变也创建一次版本occurrence。
故W的二十二次内部写及其之间六次读取全部可区分。
实际alias指向同一个identity顶点；相等内容的不同birth各有顶点。
未初始化、unlinked、status0、partial records均在图内。

逆沿唯一event spine恢复顺序和缩减项，
从G求值并全检每个版本、terminal、incidence及引用端点。
图不能有遗漏的birth、未列event、假alias或无来源版本。
完整检查后输出求值的 $X_r$；仅给当前AA逻辑树的图不是这种空间体。

**定义 67.4（边界体 $\mathsf B_r(H)$）。** 边界体是按真实顺序复合的literal primitive boxes。
每个box有所有实际read／write／test／control／I/O／birth／journal terminals，
携真实名字、before／after field版本和内部访问次序。
unchanged field、alias和grant用真正carry wires贯穿；G及完整最后raw boundary均保留。
W二十二写的版本在一个原子ENTER box内部，不据此宣称新增可进入的cut。
carry域在这个有限prefix上有限，生产每条wire要实际扫描和写入。

逆按保留顺序切开boxes，完整检查terminals与carry／alias／grant连线，
取缩减项后重新求值，全比每盒及最后raw boundary。
这是一种完整内部event-interface表达，不能换成旧外部traffic-only boundary。

**定义 67.5（记忆体 $\mathsf M_r(H)$）。** 记忆体是G及从旧cut实际可达的immutable
缩减journal-node heap，保留真正node identity、prev、完整允许payload、
固定inventory binding槽及read／retention模板关联。
它不把派生private effects伪称为这些节点已有字段。
节点copy的destination身份与被复制的真实node身份区分。

逆全检prev链、typed节点及固定登记模板，倒序收集再反转，
用第65节求值，因而派生包括W在内的完整效果、rights描述及费用。
reserved／unlinked材料由它们的实际birth重建，不因完成root不可达而遗漏。
这条逆不读取 $\mathsf T_r$ 或其他已生产body。

**定理 67.6（四种结构各自完整）。** 对每个实际有限 $H$，
若 $\mathsf{Body}_a(H)$ 是定义67.1对相应实际结构的完整序列化，则

$$
\mathsf{Dec}_a(\mathsf{Body}_a(H))=X_r(H),
\qquad a\in\{\mathsf T,\mathsf S,\mathsf B,\mathsf M\}.
\tag{AS67.1}
$$

证明。$U$ 的首个0唯一界定自然数，$B$的长度唯一界定每个字，
type／init／null tags与schema次序唯一界定每个field；
对list长度归纳给完整有限结构的唯一解析，exhaustion排除尾随数据。
这是普通injective finite codec方法在这里的应用。

时间体直接给实际顺序及缩减项，且第64节求出的所有terminals正是其所列，故全检查通过。
空间体的event spine给同一顺序；每个birth及版本的incident terminal
按定义连到真实对象与实际值，因此恢复同一个缩减链，
重新求值给同一个版本关系，所有alias及uninitialized检查通过。
边界体切开后，每个box的literal tag、外参及binding仍完整，
carry保留此前未写字段，内部访问序保留同一步多次写，
所以恢复同一缩减链且终边界与求值一致。
记忆体的真实prev严格倒向同一入口，反转恰给 $R(H)$，
固定inventory自登记只需模板验证，不引入另一条效果输入。

四条逆因此均以同一个G、同一个真实缩减链调用第65.3定理，
得到实际名字下的同一个 $X_r(H)$。
每条逆还验证了自己完整的结构，不把“有一个编码”当作该图或边界的真实来源证明。$\square$

**定义 67.7（互表示与取得的区别）。** 在这个实际image上，
$\mathsf{Enc}_d\mathsf{Dec}_a(\mathsf{Body}_a(H))$ 给同目标的 $d$ 表达。
这只是数学转换，不给独立producer、真实delivery、当前grant或return。
四体的“独立”指逐体可逆且分别实际生产／取得，不指统计独立、四个独立source或最短表示。
下一节另证四次真实生产，而不以这个转换方程替代任何一次。

## 68. 四条独立付费生产与完整实收

**定义 68.1（四条实际生产路径）。** ENTER后，
当前capsule通过自己的实际allocations构造localRoot、channel／peer／queue／backing及workspace，
再接收合法post-wake request frame。这些records不同于W的 $s,v,r,d$。
每个bit经真实IN占latch，完成backing才清空并开放下一位；
length、body、ending及ACK各有持续cursor与partial状态。

时间producer作一次新的Collect与Eval，
把完整派生有序效果写入自己的表，再按定义67.2逐项emit。
空间producer另作新的Collect与Eval，
用完整identity扫描建立实际object／endpoint及event顶点，
逐access建版本与incidence，接实际总前驱spine，独立序列化。
边界producer第三次独立Collect与Eval，
为各规则构造literal box与全部terminals，
以完整表扫描构造每条carry／alias／grant wire，再独立序列化。
记忆producer第四次独立收集真实旧缩减heap；
用自己的Eval检验节点／prev／登记模板及来源，序列化定义67.5的实际缩减heap。

每条路径输入只有G与同一冻结R，互不读取其他body或另一次已解码表。
四个collector、evaluator、workspace、serializer、mailbox、session与requester destination均为各自实际工作。
四个destination不alias；图的identity去重不合并这些真分配。
M的求值用于核验来源，不把T的完整效果偷偷填成M节点字段。
所有scan、map、计数、版本、wire、长度与表示访问均是实际字段／bit行。

**定理 68.2（四条生产分别有限且同源）。** 在无child干扰的一次处理中，
四个producer分别有限产出定义67节的完整body，且来源都是同一个 $H$。

证明。冻结cut的链有限，第65.2定理逐条给各自Eval完成。
时间输出扫描有限effects表；
空间构图对有限identity表作有限次全比较，
每个event有限access，故版本／incidence总数有限；
边界构图对同样有限event与field集作有限次wire扫描；
记忆路径独立沿有限prev链读全部真实节点。
各counter和字长有限，codec长度取得及输出有限，
故H-F本地进展下四者完成。

第65.3定理对各次输入分别成立，故时间表为真实effects，
空间alias只按真实identity合并、顺序为真实spine，
边界terminals及carry来自同一逐行状态，
记忆节点来自实际旧heap而非别体的产物。
每一生产新生成的日志都位于旧cut之后，不能变更任一输入范围。
因此分别是所定义实际结构，不是将一个先取得body换四个tag。$\square$

**定义 68.3（全bit交付机）。** 每条delivery有自己的真实sender／receiver／connection／backing。
sender先发完整length frame，再按cursor发全部body和ending；
receiver每次只在指定phase接收，IN后保存该bit，
写入对应destination backing后才清latch、推进cursor、重新开放。
destination在完整length、全部body、ending及exhaustion完成前保持未seal。
每次delivery的genuine ACK按自己的方向、origin与stage执行，
不能用parent ACK、原input或别次同值bit替代。

**定理 68.4（实际收到的四个逐体逆）。** 对四条真实交付，

$$
\mathsf{Recv}_a(H)=\mathsf{Body}_a(H),\qquad
\mathsf{Dec}_a(\mathsf{Recv}_a(H))=X_r(H).
\tag{AS68.1}
$$

每个等号关于全字及其真实destination，非只关于一段prefix。

证明。对每条route的协议位置与phase作归纳。
起点length cursor为0、destination未seal。
sender本阶段只可发送当前位置的实际bit；
receiver IN得到的正是这个连接bit，occupied latch阻止二次接收。
backing写在同一cursor位置，写完才推进，所以无跳位或重复。
此过程归纳覆盖length frame、body的每个位置及完整ending。
length和exhaustion检查使receiver既不少收也不多收，
完成后才seal并接收该delivery自己的真实ACK。
H-F供应这些有限合法traffic与进展，故归纳实际走到终点。
这复用TMC PR57.D7／L4的exclusive bit-copy论证，
但本字段程序的source、workspace和协议不同，不借旧 $8k+4$ 为其总价。
第一式成立后逐体用第67.6定理得第二式。
producer来源由第68.2定理给，不能由“报了origin字”或codec等式单独给。$\square$

## 69. 完整所选实收体驱动的真实返回

**定义 69.1（完整selected return与全验证）。** 四份都完整取得之后，
requester才选择 $a\in\{\mathsf T,\mathsf S,\mathsf B,\mathsf M\}$，
通过新session发送其实际取得的完整块：length、所有body bit、ending及规定ACK阶段。
不能只发送choice index，也不能送一个producer缓存的答案。
支持receiver以新backing按第68节的latch纪律接收整个selected body。

Verify全解析kind、source／genesis／install／schema、cut、parent、
所有长度／tag／typed identity／uninitialized／null、ending及exhaustion；
要求cut等于 $c.\mathsf{cut}$，切口parent等于目标中的Active。
再付费逐bit全比较这个实收块与该kind真实已发的完整块。
比较块只用于验证，不作为回写值或parent参数的备用来源。
合法traffic假设不推广为敌意writer／损坏信道的密码认证。

之后运行一个与producer工作表分离的received decoder，得到 $\widehat X$。
T逆检查全部时间terminals，S逆检查spine／versions／incidences，
B逆检查全部boxes／wires；M逆在新workspace再次由实收缩减heap求值。
这些都从实收字读取，不从producer已算好的 $X_r$ 复制结果。

**定理 69.2（全实收验证与独立解码）。** 完成上述合法selected return后，

$$
\widehat X=X_r(H).
\tag{AS69.1}
$$

证明。第68.4定理给requester真正持有的完整块；
对新的selected session再作同一length／bit／ending／backing归纳，
支持端实际收到的字与这个块完全相等。
全验证因此通过，不以短prefix或相同terminal答案替代。
独立decoder消费该完整字，按第67.6定理给式(AS69.1)；
即使producer表未被任何返回路径读取，这个证明仍成立。
四份不完整或traffic未完只有raw prefix，不提前产生成功decoded值。$\square$

**定义 69.3（真实身份解析与当前授权）。** 取

$$
\widehat p=\mathsf{Active}(\widehat X).
\tag{AS69.2}
$$

对decoded运行context中的每个identity，
以全部identity bit及type扫描 $H$ 冻结的实际inventory，
由匹配entry取已经存在的真正typed binding／endpoint。
扫描是有限逐项全比较，不按地址数、body相等或名字相似定位。
之后另检查当前custodian对该held endpoint的实际授权。
历史rights描述、费用和retained表完整解析为数据，不作发grant或回退账的指令。

切口所用parent及其context引用均已在H出生，故不必搜索未来inventory。
当前child／key是另有真正live binding的操作数，旧body不声称含它们。
$c.\mathsf{parent}$ 只可作一致性guard比较；
LEAVE的parent值必须来自式(AS69.2)实际解析出的binding。

**定理 69.4（解析终止且不制造能力）。** 上述解析有限，返回正是decoded实际identity，
但不从字创造任何新权。

证明。inventory端点固定在H，其entries有限，birth登记完整包含unlinked及未初始化对象。
每个完整identity比较有限，实际身份唯一给至多一个type匹配；
式(AS69.1)保证所需旧引用确在这些entries中，故扫描找到真正binding。
之后的当前授权检查使用H-234保留的实际custodian权，
而非decoded grant字段。
new child births及扫描自日志不延长搜索范围。
因此全扫描有限，匹配只选择旧endpoint，不执行allocation或grant。$\square$

**定义 69.5（逐项实收操作数回写）。** 按有限typed schema枚举
$\widehat p$ 的PC、latches、reference registers、实际head及声明的参与者control字段。
每项的目标identity和值只从received decode取得，
经过定义69.3真实解析及当前授权，再作一项真正行政写。
原source edges、payload heap、根槽、tokens、grant与变量环境留在原处，
不进行whole-state反序列化。
Native head项解析真正marked cell，写该cell mark为1，其余held marks不动。
列表、next cursor、comparison cursor及每个partial write均保存在当前restorer heap。

**定理 69.6（逐写幂等与恰一次线性释放）。** 回写有限完成并执行

$$
\mathsf{LEAVE}(c.\mathsf{key},\widehat p)
\tag{AS69.3}
$$

后，选回同一父活动和同一owed action；新的全局历史及wake状态不回滚。

证明。以context列表已处理项数归纳，保持：
已写项等于received decode值，未写项和其他父heap仍等于进入值，
backed next cursor指向下一实收项。
起点由第66.2定理；每个decoded值由式(AS69.1)恰等于进入值。
第69.4定理给同一个真实目标及当前write权，
故该项写后仍等于旧值，归纳断言保持。
head指定cell在进入时原已mark1，其余mark被held，
故写1保持唯一head，不偷移到相等内容cell。
每一幂等写仍是一项实际收费occurrence。
列表有限，完全扫描、比较及写在H-F下完成。

若child在中途进入，它的parent是这个partial restorer。
它先返回同一个restorer及其next cursor；
不能越过这个restorer去释放更低ancestor。
第70节的有限森林归纳据此保持同一个逐项断言。

LEAVE按真实top／key.child／parent／unspent和当前custodian权检查，
一次原子地spend当前key、retire child、select式(AS69.2)解析的parent。
之后key已spent且child不再Active，普通write无权重置它；
因此这次释放恰一次，不能花ancestor key或重放同一release。
LEAVE本身不执行父动作。

重新选择的原解释器／driver真正读取已写PC／latch／register／head决定下一动作，
所以实收数据进入活执行路径，而不是旁边未使用的审计体。
pre-IN若已有genuine buffered bit，原sender及bit一直held，原IN随后只消费一次；
post-IN／pre-WR则保留occupied latch，返回的是WR，不重复IN或提前reopen。
缺input的原IN仍pending。有限干扰结束、原guard及进展满足时，同一owed action发生一次。
新journal、inventory、W的最近backing、child档案、spent key、constructed capacity及费用
均不在回写列表内，继续保留；历史 $X_r(H)$ 没有被整块写回live世界。$\square$

## 70. 全部部分切口与任意有限请求森林

**定理 70.1（raw边界的自适用闭合）。** 第65–69节适用于定义60.2每个真正到达的covered cut，
包括全部原及支持内部partial状态，不要求Ready、sealed、完整pool或非null localRoot。

证明。任取一个cut，H-W在这个cut给真正当前授权handoff，
第63.2定理给ready；没有先筛选“已经幸运可wake”的cut。
按源schema检查raw状态：allocation一完成即有binding及未初始化字段，
inventory按birth登记，所以未link或status0仍可重建、解析。
SOURCE-template／Reserve／Maintain的cursor、source／parent及pending append均在heap，
head已链接而tail未写时重建的就是那个partial字段关系。

十二TOK第一项后，owner分裂及下一TOK保留；支持不用原pool，故不要求先补第二项。
genuine ACK IN后、backing WR前，先前OUT及IN均在目标，
bit仍在occupied latch，owed action为WR。
variable-depth decoder将冻结INPUT与自己STACK分开，
未完成的length、半字、ending、parse frame及未seal结果均为实际raw字段，
不以完整语义树替代。

Collect／Eval／graph／version／wire／Emit／DeliveryACK／SelectedReceive／Verify／Resolve／Reinstate
都只有固定finite控制，动态map、stack、余量及cursor在heap。
child捕获这些partial软件状态与捕获原driver使用同一field规则；
历史重建只模拟已经发生的一行，不调用未完成producer的未来答案。
partial restorer返回它自己，再继续下一项回写。

ENTER之前可请求；ENTER之后没有待执行save prologue，
null localRoot本身是定义完整的Entry，紧接子请求由第66.1定理给出。
pre-LEAVE仍有unspent top key；post-LEAVE的parent已经是新Active，
没有spend后尚未select的额外软件缝隙。
receipt与journal是声明的固定原子coeffects，
其普通复制／解析过程仍逐步可请求。
这些穷尽第64节有限schema的所有前后边界，不删去任何普通软件cut。$\square$

**定理 70.2（所有有限有序森林）。** 在H-W、H-F及其余假设下，
每个有限有序请求森林都有限处理，逐node给四个实际完整received body及第69节真实返回；
每个root后回到其进入cut的同一owed action。

证明。先对请求树作结构归纳。
叶请求的旧prefix有限，第65.2定理给求值有限，
第68节给四次独立生产及全交付有限，
第69节给selected全重传、验证、独立decode、identity／right检查、个别写和LEAVE有限。
这些步骤不等父完成或消费父input／ACK。

设一个node有有限多个按实际到达次序排列的child。
父在child前已执行的本地前缀有限；
第70.1定理使那个partial cut合法，归纳假设给child有限完成，
第66.2及69.6定理使父的heap、cursor、owed action及权限原样接回。
于是父继续本地程序的下一步。
逐个处理有限children后，父的本地进展论证与叶相同，
所有循环输入端点都冻结，不随children新日志延长，
故父剩余本地工作有限并正确返回。
这一论证在局部进展证明中可把child替换为一个“返回同frame”的有限区间，
但实际 $X_r$、日志、材料和费用中保留该区间全部效果，不能删除账。

对有限多个有序roots再归纳，逐个回到原活动。
树高和宽度仅影响有限数据及真实工作量，归纳不改变安装或引擎。
原动作在有限干扰后按原guard／input恢复；若缺input，
结论恰为继续pending，而非凭森林终止就伪造一次执行。
这证每个有限森林，不推出无限请求流的终止或统一时延界。$\square$

## 71. 原source投影、完整ordinary与准确旧分支

**定义 71.1（保留实际来源的投影）。** 对 $J_r$ 的实际联合历史取 $\pi$：
删去support-only行及新增journal／inventory／gate coeffects、ancestor被停区间，
保留每个原boot／安装／source／controller行，
每个真正原external ingress、sender OUT、receiver IN／backing、
原record与原receipt及其实际顺序和binding。
原Native occurrence的旧receipt保留，只删它新增的缩减coeffect。
按实际type／owner／source归属投影，不按bit值或“是否已被接收”删sender。
状态投影只取原schema字段、原权限及其实际binding，忘掉新增行政字段，
不重命名或重绑定任何原对象。

**定理 71.2（同一实际原组件的双向对应）。** $\pi$ 的结果是同一个原组件的合法执行；
反过来，任一声明域内原有限adaptive schedule
都允许在真正到达的covered cuts插入任意有限请求森林，
在H-W／H-F供应下保留同一个原下一动作及原输入域。

证明。入口后保留的原bootstrap确实使用同一 $\xi$、Native beta及其真正未知输入，
四次allocator return给原互异 $O,F,N^*,r_0$，
O的七个事件、固定根槽／driver、原ports／tokens、
非null parent及共同祖先append均是该source的原次序。
支持既不改root slot，也不换成相等body的新源。

对保留的原occurrence数归纳。
设前 $k$ 项的原状态已为原source允许状态。
它们之间的support普通步只动自己命名域／公共新增记录，
W只动独立插座，第66.2定理阻止原参与者推进，
第69.6定理的行政写在原运行context上逐项幂等。
LEAVE只select而不执行原动作。
所以下一原行见到与前 $k$ 项决定的相同PC、head、latch、operand、
owner／right、真实连接、guard及source binding。
以同一个真正外来输入应用原literal源律及旧receipt，
得到该原行实际后继，归纳成立。
先前OUT／backing不因尚未IN而被擦除或移位；
disabled none不是事件，执行过的refusal、partial状态或fault也不变成成功。
因此只对这个合法投影复用既有无support完成定理，
不声称增广全历史、raw世界或费用等于原历史。

反向给任一原schedule和所指定实际cut。
H-W在该cut供应当前授权真实wake，不需先做原owed action，
第70.2定理给有限森林及同frame返回，
之后按原guard与input执行同一个下一原行。
依次插入有限roots即可。
若cut属于插入后的support过程，第70.1定理同样给合法进入。
有限树高无需预装代码或更多engine。
所以没有缩成idle、完整对象、已存wake或恰好已有input的子域。$\square$

**定理 71.3（完整ordinary消费者链）。** 对定义60.2每个ordinary实例，
$J_r$ 保留式(AS60.1)、每个完整Entry的 $E(t_i),h=K=w(t_i)$、
由真正Y选择的同一个实际descriptor，
并保留AS28.4、29、34.4、36.4的完整原取得、结算与下一轮消费者。

证明。由第71.2定理，投影中实际Init、初始cone、acquisition／ACK／carrier及首次Entry
正是AS28.4所给原程序。
其根、AA的P／S、Navigate／Guard／Reserve、真正creation binding
和每个祖先Maintain仍在同一source，不以raw-reference捷径取得完成body。

设前一完整Entry已成立。
AS29、36.2的下一真正raw／guard阶段收到实际 $A_i,v_i,g_i$，
原candidate Build／ReadBody或old-frontier Rho逐行执行。
完整canonical prefix decoder／converter、P21 backing、Q context、
raw materializer与其refusal、Plan／Reserve／Raise、Companion20及先前receipt全copy，
packet／F7／referent／holder／Assoc都保留原输入和原消费者。
Input22及28／8／10变量深度parser／forest、
BIND／code／全部arms解释、full MUX、ordered STORE、cleanup／release
均在投影内真正发生；原Y／J／U、indices、sidecar及dependencies没有由support decoder代替。

AS34.3–34.4的整个M catalogue和完整FAM-ACK echo、
真正Done8、carrier、source TOK／idle及NEW response状态照原结算。
必须在全部settlement／ACK之后，用fresh Close29
重新载入这次捕获的同一个NEW response状态。
AfterFinal才从这个状态读真正Y、更新state／counters，
执行原十二reverse TOK、role CTL、真正Tail13／17及Entry。
旧LatestType或helper residue不替代这次NEW；
下一speculative edit也不能跨过未完的前次settlement。
因此真正Y决定accept时保留候选、refuse时保留旧值，
给式(AS60.1)及对应的同一个descriptor。

support森林可以插入上述每个已到达prehalt cut，
但第70.2定理只延迟并返回原下一行。
原adaptive choice因此仍可根据先前真正收到的完整response作出，
没有被support回答代替。
对 $i$ 归纳得到每个有限horizon及任意非空有限operand。
$N=0$ 时初始carrier直接走原finish，不插入不存在的candidate、final结算或额外Entry。
故全ordinary消费者链而非单个逻辑递推保留。$\square$

**定理 71.4（准确mode10及各类退出）。** $J_r$ 的mode10保留定义60.2的全部guard分支，
mode00／11和原raw／local／fault退出保持原图，且没有新增任意内部策略定理。

证明。由原投影应用AS37.1。
C0实际guard2；C1的实际Left候选为原F所承载的 $\langle C,C\rangle$，
guard2拒绝留O，guard4接受选F。
C1全settlement、同一NEW reload、AfterFinal、Entry、Select之前没有C2输入。
C1拒绝后C2是Right(alpha)，guard2拒绝，所有有限guard至少3接受；
C1接受后C2是Rho，guard4与5拒绝，所有有限guard至少6接受。
$r_0$ 的真实alpha／idle未触动，不用它冒充O、F或 $N^*$。

其余模式及退出同理由literal投影保留。
accept、executed source refusal、strict／unchanged／maintenance-refusal、
合法nonmodifier domain exit、BadFrame／FaultHeld、
busy／missing-right disabled none、partial ingress／status0及absorbing halt
有各自原标签和后继，不能合并成一个“未改变”。
畸形原frame按规定drain／reason／FaultHeld处理，已经committed效果仍在，
不虚构Y0、缺失行、settlement或Entry。
原input未到只给pending prefix。
这些是原限定域上的复用，不给internally generated independent guards、
all-seven direct schedule或任意internal policy。$\square$

## 72. 原Handback至INITIAL的完整终端消费者

**定理 72.1（原终端链及恰一次消费）。** 定义60.2的genuine finish之后，
$J_r$ 在原供应条件下完成同一个实际Handback／Stop／snapshot／verifier／consumer链，
真正消费一次原INITIAL-$q_1(\beta)$ 并到global absorbing halt。
全部已到达的prehalt终端cut仍可接纳有限请求森林。

证明。先在同一个原complete Entry保存原HandbackPending。
实际Park与完整ParkACK echo完成后，才作新的Close29，
重新载入这个同一个saved HandbackPending，
再执行原十二reverse TOK及Handback。
它不能用旧LatestType、另一次pending状态或捕获表达代替。
第71.2定理保留实际顺序，故AS35.2及
[RG9.1–9.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REENTRANT_GUARDED_ACQUISITION.md)
对其同一操作数适用。

这些既有证明给完整configuration／waiting-word的真实全copy、
真正table24定位、invocation转交及fresh legitimate loan，
使实际原解释器到原Stop。
Stop真正写并seal原tuple $(0,B,1)$；
这里的 $B$ 是原Stop操作数，不是支持边界表达 $\mathsf B_r(H)$。
route49输出整个tuple及其dependencies，不只发一个标签或相同答案。
随后实际Halt row、原J／U、route48交付、冻结indices及SEG-P1按原顺序完成。

route50再向原verifier交付整个冻结snapshot。
其真实enumeration、prior／INITIAL检查及accepted SEG-R1
在原当前权限和合法输入下执行。
snapshot固定的输入尾不因后来的snapshot读数、原receipt或support日志增长而延长；
这些后来的工作仍有真实账，不能因为不在snapshot中就消失。
route51交付完整bindings／receipt到原consumer，
原43目标实际取得整个copy并执行其OUT。
全部terminal ACK及token-return保留原方向、source、阶段及consumer。
因此这些动作仍是原证明所识别的INITIAL-$q_1(\beta)$ 消费，
support decoder没有接替Y、settlement、Handback、verifier或task output。

Park、ACK已IN未back、Stop／Halt构造、
snapshot／verifier及43 copy／OUT等每个真正到达的prehalt边界，
由第70节可插入任意有限森林并返回该阶段同一个下一literal动作。
它们不要求终端过程先完成。
原invocation离开RG一次，terminal图没有返RG边；
global halt吸收并同时禁用ENTER与普通support。
所以无posthalt请求、重入、第二invocation或第二INITIAL消费，
而每个原终端ACK／token-return在它自己的guard下完成一次。$\square$

## 73. 入口、原语与缩减日志的互斥发票

**定义 73.1（同次非负向量及唯一入口）。** 费用坐标按原Native、原AA、
auxiliary opcode、owner／purpose、reference-bit访问、material、grant、
automatic gate、ENTER／LEAVE和缩减journal分开。
固定同一组原与新增tariff参数，不设任意exchange rate，不把未指定tariff变成数值whole-run价。
每个原private动作、原fee／receipt及mandatory backing都保留。

令 $\mathcal A_{\rm gen}$ 恰为真实 $z_0$ 的不可约材料：
原primitive meter boundary／control、finite recorder／gate／bootstrap、
基本Active／selector、空journal／inventory根、
primitive W root及其中实际已有的基础typed binding／grant表示。
$C_{\rm gen}$ 是这批材料的入口供应向量，
$S_{\rm gen}=S(z_0)$ 是其真实保留量。
L为null、无node、原receipt为零；未初始化不视为零。

安装后的literal code／table、普通tape boundary／backing、
入口未有的grant／link／endpoint表示、
W四records与十二数据写、四个AA根／drivers／O七事件、
Native未知seed／code／input／saved client、Lift／Init及EnableCapture
全部属于 $z_0$ 以后实际行，不另设一份flat boot包。
若发票显示 $e_0$，它只能是 $C_{\rm gen}$ 在 $H$ 外的别名，
不是可执行或可记日志的occurrence，也不能再进 $\delta$ 和。

按真实birth／extension分区所有实际新供应材料：

$$
\mathcal A(H)=\mathcal A_{\rm gen}\ \dot\cup\
 \mathop{\dot\bigcup}_{i=1}^{m}
 \bigl(\mathcal A_i^{\rm core}\ \dot\cup\
       \mathcal A_i^{\rm gate}\ \dot\cup\
       \mathcal A_i^{J_r}\bigr).
\tag{AS73.1}
$$

后来extension只把新单位归新行；alias、初始化、覆盖或同值写不重生旧capacity，
却仍有实际访问／操作费。
入口已有root不重收供应，后来安装其code／grant／backing照实际新材料和工作收费。

**定义 73.2（三个互斥动作角色）。** 对真实occurrence $e$ 及实际前态 $z$，

$$
\delta(e,z)=\delta_{\rm core}(e,z)
          +\delta_{\rm gate}(e,z)
          +\delta_{J_r}(e,z).
\tag{AS73.2}
$$

core包含原或新增literal本体及适用的原Native receipt；
gate只收本次invocation的自动group／current wake／authority检查；
$J_r$ 只收一次缩减节点、字段、endpoint／retention grant、inventory登记和tail coeffect。
每个实际访问／构造按角色恰归一处。
显式软件inventory／capability测试是自己的auxiliary core行，
不同于automatic gate；ENTER／LEAVE本体tests／writes不再归gate。
opcode次数与被访问bit／材料量可列不同坐标，不把同一供应或访问重收两次。

缺原input的disabled IN不是一次IN或原receipt；
真实执行的显式failure检查只按自己的literal行收费。
owed原动作在真正执行时收费，不因capture时被悬置就预收一份虚构receipt。

**定义 73.3（安装、ENTER、LEAVE与日志的完整费用）。** W安装收四次真正allocation、
type／endpoint／grant与reference backing、root／source／custodian links、
十二次ready／empty／null／backing初始化、实际source code／schema／control及enable检查／写。
每项是H中的真实postentry行，并附其自己的gate与缩减coeffect。
预有primitive根不重复供应，早先sender工作不被这张安装票吞掉。

ENTER按式(AS63.3)逐项收费：
九次ready字段测试、六次value读、二十二写（七reference、十五finite）、
真实link解引用、旧Active／L、$c,k$出生、
allocation header／endpoint／grant、十八capsule及三key数据写、selector，
以及genuine send／receive／backing与实际origin／reference宽度、extension。
实际同值覆盖仍收write；旧 $d$ 被覆盖的前态由第63.3定理得出。
$e_{\rm enter}$ 排除和中已计部分，automatic gate和一个 $J_r$ 另加一次。
内部22写及6读不是额外28次日志，也不是Native ticks。
LEAVE另收top／key／parent读取比较、spent／retired／selector写与表示访问、
它自己的gate及一个缩减coeffect；不借ENTER的票抵扣。

journal费收真实node／segment／backing birth、
实际 $b_{J_r}(e,z)$ 位的允许tag／actor／prev／外参／binding payload、
真正reference宽度、grant／inventory及tail访问。
$b_{J_r}$ 是这一次固定元数缩减tuple的真实表示长，不是统一常数，
也不暗添完整private effects。
coeffect为自己所有出生与登记收费一次，不递归logger。
以后读取／复制这个node另有真实普通工作，不能复用出生票。

**定义 73.4（不能省略的实际工作）。** 除原boot、ingress／guard、
source edit／navigation／ancestor维护、candidate、parser／MUX／STORE、
settlement／records／receipts、saved-state reload与全部terminal消费者外，
以下均计为真实动作及材料：

- 四次分别Collect／Eval，模拟maps、effect／version表、identity去重全扫描、
  比较、counter／stack、S incidence／spine、B terminals／carry／alias wires、
  M节点读取与模板检查，四次serializer／length／framing及各自workspace。
- 全部mailbox／destination／peer session构造，逐bit OUT／IN／latch／backing／reopen、
  length／ending／status／seal／ACK；所选body再次全传输及接收。
- 全grammar／source／cut／type／exhaustion／完整判等，
  分离的received decoder／Eval，冻结inventory全扫描、完整identity比较、
  当前authority检查，每项实际行政写、key spend／retire／release及真正cleanup。
- 每个上述软件行自己的automatic gate与缩减coeffect，
  它们真正新增的日志／inventory／backing、实际reference／origin表示及所有保留capacity。

Eval、Resolve、copy、compare、length、arithmetic、seek和restore在此均指有限field／bit loops。
没有免费lookup、单位宽identity、whole-state snapshot／restore或由字生成的grant。
TMC旧copy-loop的 $8k+4$ 不成为这个完整程序的价格。

## 74. 全prefix加法、后段cocycle与同时peak

**定义 74.1（实际历史的累计量）。** 对实际
$H=(z_0\xrightarrow{e_1}\cdots\xrightarrow{e_m}z_m)$，定义

$$
C(\emptyset)=C_{\rm gen},\qquad
C(H)=C_{\rm gen}+\sum_{i=1}^{m}\delta(e_i,z_{i-1}),\qquad
P(H)=\max_{0\le i\le m}S(z_i).
\tag{AS74.1}
$$

$S(z)$ 按真正identity计同时保留的唯一材料／constructed capacity：
genesis、原source／mandatory backing／archives、
code／control／grant／wire／reference、held ancestors、所有partial工作、
W root／records／backing、immutable journals／inventory、
四份同时保留的body／mailbox／destination与maps／graphs／serializer、
selected received body、decode／resolution／restoration表及retired frames／keys。
alias算一次，字相等的真正不同allocations分别算。
clear／null／cleanup不退capacity，除非该source真正release材料。
一个原子ENTER内实际构造并保留的capacity／backing进入其后态 $S$；
内部access前态用于tariff，不因此增设外部cut。

**定理 74.2（实际后段的精确拼接）。** 若
$\tau=(z_m\xrightarrow{f_1}\cdots\xrightarrow{f_k}z_{m+k})$
是这次实际执行的后段，则

$$
\begin{aligned}
C(H;\tau)
 &=C(H)+\Delta C(\tau;z_m)
  =C(H)+\sum_{j=1}^{k}\delta(f_j,z_{m+j-1}),\\
P(H;\tau)
 &=\max\left\{P(H),\ \max_{0\le j\le k}S(z_{m+j})\right\}.
\end{aligned}
\tag{AS74.2}
$$

若 $\tau;\upsilon$ 也是实际拼接，则

$$
\Delta C(\tau;\upsilon;z)
 =\Delta C(\tau;z)+\Delta C(\upsilon;z_\tau),\qquad
\Delta C(\emptyset;z)=0.
\tag{AS74.3}
$$

这些式子覆盖安装中途、EnableCapture、ENTER／LEAVE前后及真正halt的同次出口。

证明。第65.3定理给每步真实前态、内部有序访问前态、
实际birth／extension／width、旧receipt和新coeffect，
故第73节每个tariff参数都来自这一次执行而非另一run的bill。
式(AS73.1)把入口与后续材料互斥分开，
式(AS73.2)把每步访问／构造角色互斥分开。
所以空prefix恰为 $C_{\rm gen},S_{\rm gen}$，第一boot行不重收入口，
每步也不漏旧private工作或重复旧receipt／journal材料。
按真实步累加即为式(AS74.1)。

把同一有限和在第 $m$ 项处切开，得第一拼接式；
再切后段得cocycle，后段不另加genesis。
把同一有限最大值的索引分为旧段与新段得peak式，
共同边界 $z_m$ 在两个max中出现无须将材料相加。
任一时刻held ancestors、child、旧archives及四份body真正共存，
全在那个 $S(z)$ 中；不能把分别最小的peaks拼成这次执行，
也不能用LEAVE撤销sender、记录、已收费动作或constructed capacity。
真正halt的core、适用旧receipt及缩减coeffect收一次；
吸收halt以后只有空合法后段。
这既证同次精确性，也证返回不会重置账。$\square$

**定理 74.3（原located计数仍在原位置）。** 令 $n_N(H)$ 为这次实际prefix的原Native core数。
原receipt、tick、fee仍分别为 $n_N,n_N,2n_N$。
若 $b_{{\rm control},N}(H)$ 为已构造且未另计cell的原control／code位，
$A_{{\rm nonmeter},N}(H)$ 为已构造原nonmeter cells，
则原Native的located材料式仍为

$$
S_{0,N}+b_{{\rm control},N}(H)
       +8A_{{\rm nonmeter},N}(H)+8n_N(H).
\tag{AS74.4}
$$

完整ordinary投影中的原source／maintenance调用数仍为
$4+2N+2N_{\rm accept}$。
令 $m=N+1$ 为实际arena cones数，$j=0,\ldots,m-1$，
$P_j,S_j,D_j$ 是原相应cone的successful P／S及depth和，则

$$
\begin{aligned}
P_{\rm ar}&=1+\sum_{j=0}^{m-1}P_j,&
S_{\rm ar}&=m+\sum_{j=0}^{m-1}S_j,\\
D_{\rm ar}&=\frac{m(m-1)}2+
  \sum_{j=0}^{m-1}\bigl(j(P_j+S_j)+D_j\bigr),&
V_{\rm ar}&=1+P_{\rm ar}+2S_{\rm ar}.
\end{aligned}
\tag{AS74.5}
$$

原O有3P、4S、depth和7及12个source vertices；
untouched F与 $N^*$ 各有一个alpha vertex，故原四根总数为

$$
P_{\rm tot}=P_{\rm ar}+3,\quad S_{\rm tot}=S_{\rm ar}+4,\quad
D_{\rm tot}=D_{\rm ar}+7,\quad V_{\rm tot}=V_{\rm ar}+14.
\tag{AS74.6}
$$

这些不是 $J_r$ whole-program价、任意partial cut的免费counter或总space。

证明。每个原Native core保留且只附一个旧receipt，
第64.1定理给它的真实meter constructor，故前三计数逐次成立。
AS38.1／58.4的八bit cell表示与未重复的control分类给式(AS74.4)；
$S_{0,N}$ 只属genesis，后续cell／code／receipt按真实birth收费，
已计cell的code不再计control位。AA／support／ENTER不是原Native事件。
第71节投影保留原source调用，故AS36.4及38的调用式直接适用，
不把support eval或维护表扫描加作原Build调用。

式(AS74.5)复用AS38及AA22.1在这个同一投影上的原arena计数：
第 $j$ 个cone根深度为 $j$，各内部P／S顶点再加 $j$，
cone根深度和为 $m(m-1)/2$，
原header数为 $S_{\rm ar}$，routing／side append为 $D_{\rm ar}$，
$V=1+P+2S$ 给vertex数。
加上实际原O与另外两个未动根得到式(AS74.6)。
partial operations、wake／capsule／journal、
全部transport／return／grant／reference材料是额外实际项，
不能从这些located恒等式中消去。$\square$

**定理 74.4（逐点有限而无统一资源结论）。** 每个满足前提的有限实例，
其实际工作、符号费用向量及同时peak有限；
本结论不提供polynomial bound、统一固定capacity／latency、
数值总价、资源优势、Pareto支配或global minimality。

证明。第70.2定理给有限森林的有限步，
第71–72节和原进展前提给有限原schedule。
每行只有有限footprint及实际有限reference／origin表示，故有限和及有限max均有限。
但输入树、history、forest高度、identity宽度、journal及四份body都可增长，
没有跨所有实例的常数由上述证明给出。
删除private披露可以增加求值、比较、复制和存储工作；
本账只给实际发生项，没有比较另一个方案的逐坐标弱支配证明。$\square$

## 75. 证明归属、源内充分性与未供给的实现桥

**定义 75.1（复用关系与新增承重步骤）。** 本构造的证明依赖如下对应，
每项只在其原前提和本卷已证接口内使用。

| 来源 | 本文实际使用的内容与边界 |
| --- | --- |
| AS1.2–1.4、26–40 | 原Native／AA／component源律、原完整ordinary／mode10／terminal／费用；经第71节投影复用，不直接等同增广全chronology |
| AS49–52及本卷53–59 | 固定十八字段capsule／单引擎、all-participant门、每cut真实wake供应、F3个别操作及当前held端点、F4线性释放、冻结输入与同次账；全效果F1是被替换接口 |
| AA17.1、20.1–20.3、22.1 | 真正allocation／grant、Navigate／Guard／Reserve／Build／Maintain、head／next-before-tail及原located计数；不能由descriptor推出busy owner授权 |
| TMC PR57.D1／(PR57.03)、D7／L4 | 有限Native源表与finite-control展开、actual head／latch／receipt、exclusive全bit-copy；旧meter不是private transcript，旧copy价不是本程序总价 |
| [AIF2、4.3–4.5](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md) | 真实已知起点与实际输入下Native replay的范围；不自动给联合AA／wake源或current rights |
| RG9.1–9.2 | 原Handback／Stop／INITIAL消费者；通过第71–72节的实际对应使用，不作为任意busy capture的现成入口 |

有限literal interpreter、chronological归纳、injective codec、field-version图、
ordered boxes、全copy和finite-tree归纳是成熟方法。
有限continuation constructor携环境、一个dispatcher解释任意多动态frame的组织，
可参见本卷59.1所引Danvy–Nielsen的
[*Defunctionalization at Work*, §§1.2–1.3、3.1](https://www.brics.dk/RS/01/23/BRICS-RS-01-23.pdf)；
它不供应本题的中断权、source grant或原子ENTER。
这些方法不在本文另计为新通用定理。

新增承重内容归属这个source上的构造：
真正删除确定性效果feed后，安装完整有限W源律及付费初态／bindings／grants，
逐赋值推导wake效果与tariff，结合非wake finite source-row对应，
证明缩减输入仍恢复完整实际目标，并将该对应传递至四份真实取得、
完整实收返回、所有partial cuts、有限森林及原完整消费者。
不能把W1–W5说成旧AS50.1已经列出的sender律。

**定理 75.2（可复用serial接口的准确位置）。**
[NativeSerialMachine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean)
的serial replay接口可描述一个闭输入literal evaluator的有限执行，
但单独不给第64节联合源忠实性或第69节活返回能力。

证明。该接口的转移类型是
$\delta:C\to\mathsf{Op}\ C\ O$，
不是仅有plain next-state函数；
$\mathsf{replay\_deterministic}$ 的两个前提都是
$\mathsf{Replay}$ 推导，不是两个 $\mathsf{Run}$。
把一次已经固定G与R的求值程序全部配置、有限脚本、map／stack／cursor编码在C中，
每个elementary字段机计算用 $\mathsf{Op.localStep}$，
终点用 $\mathsf{Op.stop}$。
闭输入不需 $\mathsf{read}$ 或 $\mathsf{applyRho}$。
第65.2定理的有限计算可逐localStep、最后stop构成一个有限Run，
其中携带的Source与求值输入无关，answer word为空。
先用 $\mathsf{operational\_replay}$ 的terminal结论转成一个Replay，
再在有两个Replay时用 $\mathsf{replay\_deterministic}$ 得trace与boundary唯一。
不能跳过Run到Replay这一接口步骤。

这个接口的boundary为 $C\times\mathbb N\times(\mathsf{Address}+O)$，
本身不是完整raw heap／live rights目标。
将完整配置放进C只是一种表示选择；
它既不证明真实source行等于所表示行，也不产生source端点或行政写权。
本卷的源忠实性由第63–65节逐项证明，活返回由第69节实际授权及实收操作数证明。
以上接口对应不构成本增广的已编译Lean实例或新增kernel结论。$\square$

**定义 75.3（record／replay先例的限定作用）。**
[ReVirt原文§§4.1–4.2](https://www.usenix.org/legacy/events/osdi02/tech/full_papers/dunlap/dunlap.pdf)
支持从真实起始state及完整相关非确定输入、正确异步placement再生确定性效果的方法；
其启动用powered-off VM disk copy、同processor以及不覆盖shared-memory multiprocessor的条件保留。
它不把未知历史变成免费G，也不供应本题当前grant、wake或返回。

[rr原文第一版§§2.1–2.4.1](https://arxiv.org/abs/1705.05937v1)
保留boundary input／非确定性、实际scheduling／context-switch placement、
syscall修改memory的建模及ioctl／restart覆盖边界。
branch counts与registers本身不保证唯一定位执行位置；
其user-state replay及kernel-effect injection不等于执行本题真实原RRO动作。
两种先例都不提供本卷的all-cut acquisition、
literal pending-action return、forward progress或免费tariff。
这些引文只给限定范围的方法背景，不承担W源律或本题新grant的证明，
也不构成全球文献穷尽或原创认证。

**定理 75.4（旧障碍与较大目标仍保持各自边界）。** 定理60.5是 $J_r$ 的条件结论，
不证明未改装J、旧Native-only观察或更广来源自动具有该结论；
实际可用性、委托、原子性及较大任务中尚未供给的桥不因缩减记录而消失。

证明。第65.3定理的归纳基必须是真实完整G，
归纳步必须有封闭外来输入、真实birth、明确source律与固定coeffect。
若漏掉已擦去入口信息、未建模writer／clock或非确定选择，
同缩减项就不能由第64节求出唯一真实效果。
W的ready由已装source-law证明，
但genuine offer、当前source-bound权、fresh有限材料及原子足迹仍由H-W／H-234实际供应。
若某cut不给这些供应，前提在该cut不成立；
不能删cut、等父ACK或先执行owed action来维持原全域结论。
普通sender／queue若绕门改变held连接，第66.2定理也失去其必要条件。
收费和origin字均不能弥补这些缺项。

若将ENTER／LEAVE／receipt／journal原子基础细分，
新内部状态不属于当前source的cut集合，必须另给realization及closure证明。
本定理不给由旧菜单制造这些primitive、有限物理设备、噪声／崩溃容错、
固定宽度地址、无限请求流或统一capacity／latency的结论。
四种结构保留完整event spine或内部terminals，
没有证明更少关系、旧external-only boundary、
最小root数、最小授权、最短表示、全资源优势或global／Pareto最小性。

AS46／47的first-$P_R$实际pair及K／client可见性障碍仍在原观察map上成立。
本构造新增真实journal并改变观察纤维；
其不同AA head／tail行现在可由缩减源律重建，
不反驳“相同Native stamp不足”的旧结果。
RG、$G_H/G_V/G_O$、UAS或其他alpha／beta来源
不能由名字、相同计数或codec相容认成当前source。

AS40.3／44.3已引用的
[RCA15.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md)
历史handler finite-completion-conditional closure、
IR已声明compiler-cut的current结果，
以及[GENERAL15.5／18.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md)
和RG13.3的既有cross-entry／inherited original-Q结果继续复用，
不能笼统说所有cross-entry都未解。
它们之外，changed／new-row Q、更广mixed interiors、full terminal-task kernel、
更广internally generated guards／all-seven policies、
广泛实际alpha／beta到原consumer的桥、未增广／physical来源仍需各自义务；
历史closure也不自动给本卷null Entry处的立即current返回。
静态概率／量子／几何表述没有隐含供应当前权限、busy admission或pending-action操作数。
所以较大的持续关系恢复与最简结构目标仍有这些边界；
本卷证明的是完整声明域内的具体条件模型，不以较弱子域替代原量词。$\square$

## 追加锚（本行以下为增补区）
