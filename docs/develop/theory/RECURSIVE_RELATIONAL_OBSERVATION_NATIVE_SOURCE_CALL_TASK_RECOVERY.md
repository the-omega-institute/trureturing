# 递归关系观察：原生源调用体的原任务恢复与切口边界

## 1. 对象、来源与结论的承担范围

**约定 1.1（同一实际装置）。** 固定 ARC 的一个实际有限初始化：原始源发生 $\xi$、初始界 $H_0$、实际初始树 $u$、原始先验及客户端、所安装的 $L,G$、实际捕获和规范激活。这里及下文的 `ARC` 等简称见第 11 节。源始终是该装置的源 16，地址解释是它随实际 Reserve 扩展的同一个 $\phi_K$；语义守卫 $h$ 与已预留容量 $K$ 分开。以后供给的是任意实际供给的有限规范帧，不在初始化中放入未来容量上界、帧数、源相关建议或完成时间。关于有限前缀的结论不假设未来输入到来；关于一次返回的结论保留实际供给及每个到达的原始局部计算终止的前提。 凡复用 UAS 四视图历史核，generic 实例的原始输入完整性条件一并保留：其剩余规范原始输入固定或由实际已有输入计算；若另有外部 site 而其已消费 reservoir 不能由既有选材取得，则不在本文四核结论域。固定 entry 的定理 3.3 本身不读取未来 site。

**约定 1.2（语法与证明范围）。** 承重依据是下列固定源文与正文证明；未提供的原始行引擎不作为前提。alpha、beta 是原始语法叶；有序配对和运行含义仍由原始规则给出。

**定义 1.3（原始部分任务）。** $Q$ 恰为 AIF 定义 2.6 经 ARC 定义 11.1、UAS 定义 1.4 指定的 continuation-and-audit 任务。其原始实验包括：在原始指定 IN 处 Supply$(b)$；推进下一条原始指定且启用的非 IN 行的 Advance；原始获准的有限语义、交付与审计协议；以及只依赖已取得公开响应的有限自适应实验。一次执行的响应保留合法性、实际标签、释放的有限输出和**完整原始联合后继**。这不是全部新增端口的响应任务 $Q_G$，也不是要求输出历史。

空实验只返回 running/terminal 类型及实际终端输出。物理禁用或无权的尝试返回未执行的 `none`，不添收据。物理启用而不保持源帧规范前缀的 Supply 在 $Q$ 的合法任务域上未定义；它的实际 raw IN 仍执行 latch、控制与收据后继。两个切口 $h,k$ 的 $h\sim_Q k$ 意味着所有原始有限实验的部分响应映射具有相同定义域，并在该域逐点相等。未定义、`none` 和执行后的拒绝是三种不同情形。

**定义 1.4（原始坐标）。** 原始联合后继含 AIF 定义 2.5 的实际源、工作字、头、latch、请求与响应、控制、token、待定事件、原始日志、信道及计量。特别可从中作数学选择：原始 13 上的线块、17 上的实际描述符、原始请求工作、14/19 的统一行及其索引、原始控制的调用位置、latch 5 和原始收据链。新增 64–73、历史银行或已完成周期表 $M$ 不在本文后继解码器的输入中。选择原始坐标不等于当前 actor 已有读取它们的权利。

本文的正结果是：在同一实际装置的若干**原始行切口**上，原始后继中的保留输入足以反推出当前前缀；再直接复用既有四视图的历史恢复。新增内容在输入—实际行—完整原始后继的具体对应，不在抽象回放原理。

## 2. 独立视图与原始调用的源文接口

**定义 2.1（四个既有自然表达）。** 不另造观察。使用 UAS 定义 3.1、3.3：$S(h)$ 是实际根存储子树的 L/R 路径支撑；$B(h)$ 是两个 child 槽均空的实际终端路径反链；$T(h)$ 是从有偿入口起实际原子补丁发生的顺序词，保留原生操作数、读写输入输出、构造角色和收据；$M_J(h)$ 是指定的实际保留材料及 owner、origin、seal、availability 关系。最后一项包含已取得初始源、原始及外层输入 backing、实际读入工作与占用 latch、时钟和所选当前权利；它是跨 owner 的联合选择，不是 actor $A$ 的私有已取得内存，也不是周期表 $M$。

这些定义分别来自支撑、终端关联、反应顺序、所选实际材料，没有一个由 $Q$、答案、历史编码或核的交来定义。UAS 定理 3.2 已给出 raw $S/B$ 与物理记录的逆；定理 3.5 已在规范 acquired 域 $\mathcal C$ 上给出四个**分别**的历史核。本文只使用其结论

$$
V(h)=V(k)\quad\Longleftrightarrow\quad h=k,
\qquad V\in\{S,B,T,M_J\},\quad h,k\in\mathcal C.
$$

这不是本文新增定理。原子头关联已由实际 cursor tracks 恢复；暴露细步骤后的非 child 交接关联还需要 OR 的实际 stage/head 不变量，不能从此式自动取得。

**定义 2.2（七标签线语言）。** 令 $U(j)=1^j0$。原始线帧为三位 tag、$U(d)$、恰好 $d$ 位 payload。七个 tag 为 ReadE `000`、Rho `001`、TagRead `010`、Left `011`、Right `100`、Reserve `101`、Raise `110`。前两者 payload 空；TagRead 是任意有限地址；Left/Right 是完整上下文的既有唯一前缀码；维护帧为 $tag\,U(J+1)U(J)$，$J\ge0$。值小于、等于当前界或不能接受的源修改仍是规范输入，执行原有拒绝或相应分支。令 $\mathsf C_7$ 为这些完整帧，$\mathsf P_7$ 为其前缀集。当前帧已消费 $p$ 时，源 IN 的合法任务输入恰为 $\{b:pb\in\mathsf P_7\}$。这不安装物理过滤器。

**引理 2.3（完整调用体中的原始行对应）。** 固定任一实际到达、规范 acquired 的 outer Ready 前缀 $P$。实际供给 gate `01` 并完成其原有分派，令 $e_P$ 为进入 $F^A$ 的 header Base/setup 之前的实际切口。$F^A$ 从这里至 row ACK、source TOK、最后 idle CTL 的体，逐行使用 CAP 定义 4.6 的原始输入位置、操作数、守卫、owner、结果、记录、传送和收据；唯一改变的原始边是最后 idle CTL 的后继：它进入 InnerReturn，而不是旧 raw 图的下一帧 IN。该最后 CTL 之前的行具有直接的原始实验对应。它不与未扩展运行的时钟、静态地址或捕获代码逐字相等。

证明。ARC 定义 4.1 指定的是单独编号的完整内联，明确保持 latch 5 的实际外部 IN，并只改最后 CTL 的后继；定义 5.2 的 `01` 进入原始 header Base 前导，不把 gate 位当作 header。命题 5.5 保证体内无 compiler 赋值，历史银行 parity 只作为固定有限控制乘积保留。因而静态重编号把每条非最后行的原始 guard、core、原始控制效果、receipt 和下一原始位置逐项对应；没有新贷款或并行入口插入。CAP 定义 4.6、引理 4.7 和引理 6.7 已分别规定完整 ingress、全部七分支及行交付/ACK/source TOK。将其连接便得断言。最后 CTL 的两个不同后继由定义直接给出，所以该行不满足上述未变后继断言。$\square$

**约定 2.4（原始行域，不是所有新增行域）。** 下文正定理中的 Supply/Advance 是引理 2.3 对应的原始行，或 `00` 之后真实恢复的原始客户端行。未把 `70` 上的 gate/history IN、银行重建、bootstrap、InnerReturn 或 CaptureCAP 的行命名为原始实验。它们在数学恢复出的实际历史中照常存在并计价；其原始 $Q$ 实验接口仍须另证。

## 3. 不依赖终点 frontier 的匹配写入解码

**定义 3.1（单次调用区间）。** 固定上述完整实际前缀 $P,e_P$ 及 $e_P$ 的实际全状态作为共同参数；变动终点只给下述原始坐标。$\mathcal I_P$ 包含从 $e_P$ 开始，一帧 $\mathsf C_7$ 的任意实际可延长前缀所到达的所有原生原子切口，对每个完整延长帧 $w$ 直至该次调用的最后 idle CTL 后继 $f_{P,w}$，不继续到 InnerReturn 的下一行。它是不同实际输入的前缀树，不是假设一个预先给定的未来帧。全输入保留在 carrier；本域只作规范前缀限制。允许完整调用内的 raw 源覆盖无效字节、预分配、计数器半写、待定事件、描述符、贷款、复制、检查、ACK 等中间态。

**引理 3.2（匹配 WR）。** 在 $\mathcal I_P$，每次源 IN 前的绝对原生 ordinal 为 $j$ 时，其匹配线位的 WR 后 ordinal 为：header/length 的 $j+3$，payload 的 $j+2$。WR 地址在 IN 前已由当时实际状态确定；从 IN 到该 WR 没有另一次 IN 或 latch 5 覆写。匹配 WR 执行后，该线位在本次区间内不再改写。

证明。CAP 定义 4.6 的 header 是 `IN; EX; WR; MR`，length 是 `IN; EX; WR; RD(test); MR`。两者在 IN 前已位于当前 append R；EX 不因输入值分支，WR 把 latch 5 写入该旧 R 所成的线位。payload 已按实际完成长度 Zero 预分配，并已 At 到其当前线位；正迭代是 `RD(length); IN; WR; MR(payload); MR(length)`。故以 IN 前为 $j$ 时恰有上述偏移。length 的测试用不同 latch；两种图均没有中间输入或先覆写 latch 5。后来 WR(status,1) 只写各块的独立 status，不写线位。三个 wire 块按原始保留规则不再修改。尚未被 payload WR 写入的预留零不因此成为已消费输入。$\square$

**定理 3.3（单次完整体的旧坐标输入逆）。** 对每个固定的实际 $e_P$，只给定一个终点 $x=X(h)$ 的原始 13 字节、latch 5 和原始收据数 $n=|h|$，就可在 $h\in\mathcal I_P$ 的实际像上唯一恢复从 $e_P$ 至 $h$ 的完整实际历史。解码不读取新增端口、终点 base/counter/head、终点完整描述符或后来的事件行，也不需要未来容量、未来输入、一个当前有效树或另加 frontier 字段。$e_P$ 是定理的固定共同参数，不是声称已免费安装或交给 $A$ 的快照。

证明。从固定 $e_P$ 的实际全状态作数学逐行模拟，绝对停止点是 $n$；这个共同参数不由变动终点推断，也不作为初始化建议安装。已知行不是 IN 时，实际有限图、当时的头、字节、latch、token 和控制唯一决定下一行；所有描述符、目录、源生成、原始行和信道工作也执行其实际展开，没有额外调度选择。模拟遇到尚未超过 $n$ 的 IN，设其前 ordinal 是 $j$。模拟到此已知道匹配写地址 $a$ 和它属于哪一种 reader。令 $w=j+3$ 或 $j+2$。若 $w\le n$，从给定的终点 13 读取地址 $a$ 的保留线位；若 $w>n$，取给定终点 latch 5。

对已模拟行数归纳。起点正确。若下一行非 IN，确定性保持实际相等。若是 IN，第一种情形中，实际匹配 WR 已在终点前发生，其后不覆写，终点线位正是该次实际输入。第二种情形中，已发生 IN 而尚未到 WR；引理 3.2 保证直到终点无另一输入和 latch 5 覆写，故终点 latch 正是该输入。两种选择都等于实际位，所以下一步和其收据都正确。归纳至 $n$ 得整个实际前缀，包括未完成 ingress、源无效覆盖和所有下游阶段。若两个实际像给出相同三项数据，以上确定性算法得到同一个前缀，因而唯一。

算法不把未来零当输入：只有判断 $w\le n$ 后才用终点线位；否则只取占用 latch。它也不先假设终点的解释树、活动目录或最终 descriptor 已成立。原始计量链提供 $n$，并非源事件数 $m$ 或回放中可略去的辅助步数。$\square$

**定理 3.4（固定 reached entry 的全调用体原任务核）。** 令 $\mathcal D_P\subset\mathcal I_P$ 为 next row 仍是引理 2.3 所述未改原始行的所有 running 切口；删去 next row 是最后 changed idle CTL 的切口及它的后继。则对每个 $V\in\{S,B,T,M_J\}$，分别有

$$
V(h)=V(k)\quad\Longleftrightarrow\quad h=k
\quad\Longleftrightarrow\quad h\sim_Q k,
\qquad h,k\in\mathcal D_P.
$$

该域包含全部七标签、全部规范 ingress 的半读入及未写 latch、所有接受/拒绝/维护值分支，以及源操作、分配、目录、计数、事件、行、信道、贷款、检查、ACK、source TOK 的实际原始阶段，不仅是 strict Reserve 的 Zero 段。

证明。$h=k$ 保持同一装置、同一状态及输入位置，所以所有原始实验的合法域、标签、输出和后继均相等，包含未执行 `none`、未来 Supply 的任务未定义及空响应。

反向设 $h\sim_Q k$。若 $h$ 的下一行非 IN，Advance 是实际启用的原始一步。若它是 IN，由规范前缀的定义至少有一个 $b$ 使当前前缀 $pb$ 可延长为完整帧，取该 Supply$(b)$。这是数学上选择一个存在的共同测试，不主张 actor 可秘密查看 $p$。该测试在 $h$ 定义且成功；响应映射相等迫使它在 $k$ 同样定义且执行成功，不得变成无权 `none` 或任务未定义。引理 2.3 保持该原始一步实际后继。两响应的完整原始后继相等，故其 13、latch 5、原始收据数相等。

两实际后继仍在定理 3.3 的解码区间内，包括下一行已是最后 idle CTL 的边界。解码得到相同的后继历史；去掉各自最后一条实际原始发生，得 $h=k$。这里使用完整后继中的旧坐标，没有把新增银行或历史表塞入响应。最后，$\mathcal D_P\subset\mathcal C$，逐个应用 UAS 定理 3.5 即得每个独立视图的两方向。这个最后步骤复用旧历史核，不算新的几何逆。$\square$

## 4. 多次实际源调用：封口域与 INITIAL 后缀

**定义 4.1（重复 source-only 的封口域）。** 固定任意实际共同 Ready 前缀 $P$，它之前可以已有增长和历史调用；从 $P$ 以后只允许 `01`、一个规范七标签源帧、完整 InnerReturn/CaptureCAP、再到 Ready 的有限重复，不插入 `1`。$\mathcal D_P^{\rm seal}$ 选其中当前调用三个 wire 块及描述符均已封口、next row 是未改原始非 IN 行且尚未到最后 changed idle CTL 的 running 切口。不同滚动 entry 可以比较，但共同的 $P$ 固定；不把不同 $P$ 的定理直接取并。

**引理 4.2（封口源帧确定 gate reservoir）。** 在 $\mathcal D_P^{\rm seal}$ 及其下一原始行后继，从完整原始请求 backing 和原始收据数可恢复实际前缀。相对于 $P$，若已经取得的辅助源帧数为 $c\ge1$，gate 输入恰为 $(01)^c$，源输入恰为这些完整帧的有序列表。

证明。从 $P$ 已知的 13 前缀末端开始，当前所述域没有恢复原始客户端，也没有 history `1`。每次进入 $F^A$ 之前恰好消费 `01`，且在下一次 `01` 前必须完成该次返回。CAP 定义 4.6 为每帧依次保留独立的 header、length、payload 三块，分隔符和 status 不属线输入。此域当前三块都已完成，故原始 13/17 给出其实际地址与 wire 值；先前块不改写。调用后的原始工作不会把响应当作另一帧，InnerReturn/CaptureCAP 也不产生独立 IN。于是这份有序列表与 $(01)^c$ 给出从 $P$ 至终点的全部变量输入。

对固定的实际 $G$、分配约定和 $P$，按 ARC 定义 6.1–6.3 的实际行关系模拟，恰在给定收据数停止。每个已到 IN 得到实际输入；新增 gate、银行、CaptureCAP 的真实行也按图执行，既不免费跳过也不重新编号其时钟。逐行归纳得到同一个前缀。此处复用确定性回放；新的依据是旧请求 backing 在这个 source-only 域上补全了新增 gate reservoir。$\square$

**定理 4.3（跨调用封口域的原任务核）。** 对任意上述固定 $P$ 及 $h,k\in\mathcal D_P^{\rm seal}$，分别对每个 $V\in\{S,B,T,M_J\}$ 有 $V(h)=V(k)\Longleftrightarrow h=k\Longleftrightarrow h\sim_Q k$。

证明。此域的原始 Advance 执行成功。若两个 $Q$ 相等，其完整原始后继相等；引理 4.2 从同一旧请求列表和收据数恢复同一后继历史，再去掉最后一行。反向及四视图方向与定理 3.4 相同。它比较的包括不同已完成 source-flight 数和不同实际有限容量，不要求源树或已提交计数相同。$\square$

**定义 4.4（固定 beta 的 source-only/INITIAL 联合域）。** 取 ARC 定义 9.1 的那一个初始化：$H_0=h=K=1,u=\beta$，先验 $\{\alpha,\beta\}$，原始已初始化的客户端只执行其 Stop，提案为 $q_1(\beta)=(0,B,1)$。从其第一个实际 Ready $P_\beta$ 以后，允许任意有限次完整的规范七标签 `01` 调用而无 history `1`，以及可选的最终 `00`。令 $\mathcal D_\beta$ 包含所有源调用的上述封口原始行切口，以及 `00` 新增 setup 完成后，从第一条原始 workspace TOK 的前驱起，经真实十二个贷款 TOK、客户端、生产者、验证器、consumer，直至最终 halt CTL 的前驱（含）为止，next row 是启用原始非 IN 行的 running 切口。终端后继不在域内。新增 `00` setup、gate、返回和 CaptureCAP 的切口仍不在域内。

**引理 4.5（原始请求来源的分类，不能仅数三块）。** 在 $\mathcal D_\beta$ 及其下一原始行后继，完整原始坐标决定有序辅助源输入列表 $F=(f_1,\ldots,f_c)$。在源调用内列表包含当前封口请求；在 stopping suffix 内只包含已完成的辅助源请求。这里使用实际请求引用、原始事件种类和当前原始请求位置，不以“13 上每三个块”作为任意控制器的判据。

证明。已完成的原始统一行有固定 `SEG-U1` 字段，其中包括 event kind 和完整 retained request reference；14 的 payload 及 19 的有序索引保存其真实原始来源。对已封口源行或维护行，CAP 定义 6.2 的这些字段指向 CAP 定义 4.6 的三块实际 wire backing；重复相同字节的请求仍有各自的实际块创建位置，不能去重。NativeLocal/Halt 行则有各自执行指令/输出类型，不作为额外外部源帧。

在某个源请求尚未写成完整统一行时，serial admission 保证至多有这一个未完成调用。它已经跨过三块封口，三块的真实描述符、保留 wire 值及当前原始 reader/请求位置仍存在；CAP 定义 4.6 在前一个 ACK 之前不接受下一源帧。可按这一实际源入口之后的三块位置补入当前请求。在请求元组尚构造中时，已封口三块本身足够，不从未写完的元组读一个不存在的完整引用。请求行封口以后以相同实际 block origins 识别它，只列一次。源 ACK 和 source TOK 之后未发生新输入，列表不变。描述符查找使用其完整原始 backing 与字段，不把 ordinal 当作运行时 Seek。

`00` 前客户端一直停放，故这些辅助调用之外没有原始客户端计算源命令。`00` 后这个固定客户端的下一指令就是 Stop；CAP 定义 8.1 与 ARC 定理 9.2 的真实路径构造输出 31、经 49 到 21 的完整终端材料，然后走 Halt、验证和 consumer。它没有 ReadE/Rho/Left/Right 等客户端源指令，也没有外部源 IN。其局部/终端记录和输出复制不是一个 `01` 请求。因此用 event kind 及原始当前请求/调用位置即可从这些材料中保持同一个 $F$。这一步没有假定停止路径不创建其他普通块，更没有以相等字节来推断外部输入身份。全部分类由现有原始请求类型、实际位置和固定 Stop 代码承担。$\square$

**定理 4.6（固定 beta 的封口源行与真实 INITIAL 后缀）。** 在定义 4.4 的同一个 $\mathcal D_\beta$ 上，分别对每个独立视图 $V$，有

$$
V(h)=V(k)\quad\Longleftrightarrow\quad h=k
\quad\Longleftrightarrow\quad h\sim_Q k.
$$

这包括“一个切口仍在源调用，另一个已经在原始 INITIAL 后缀”的比较；不需要先假定它们属于相同部门。它不包括 raw 非规范输入、前获取、任意新增阶段、暴露细 Busy 或终端之间的比较。

证明。从一个完整原始后继，按引理 4.5 取得 $F$，按原始收据数取得实际 $n$。向从固定 $P_\beta$ 开始的数学模拟提供源列表 $F$ 及 gate **超前缀** $(01)^c00$。如果目标尚在第 $c$ 次源调用内，最后 `00` 不会在停止点 $n$ 前被询问；如果目标在 stopping suffix，前 $c$ 次调用均已返回，它恰好消费最后 `00`。$c=0$ 时这是立即恢复原始 Stop。故无需从新增 70 或银行观察哪个 gate 已消费，也无需人为给予“当前部门”字段。引理 4.5 的原始调用位置只用于正确取得请求列表，不承担选择新增 gate 的信息。

固定 Stop 及其后续验证、consumer 行没有额外独立 IN；所有字、复制、输出和分支都由当前实际原始状态及固定代码决定。因此超前缀的实际已消费部分在每个到达的 IN 相等。按实际 $G$ 的有限行归纳，包含所有新增返回、捕获、贷款和原始 stopping 工作，恰在 $n$ 停止就得到唯一完整前缀。这个停止法使用的仍是既有 superprefix/replay 方法；具体新增事实是原始请求来源与 gate 超前缀在两个实际部门同时成立。

若 $h\sim_Q k$，二者定义域内的原始 Advance 响应同为执行成功且原始后继相同。上述唯一性恢复相同后继历史，去掉最后一行即可。若该行正是全局 halt CTL，成功响应仍含执行后的完整原始后继，所以论证仍成立；这不把**随后空实验**提升为全状态输出。其余方向及四视图结论由确定性和 UAS 定理 3.5 给出。$\square$

**命题 4.7（一般源/客户端提案的准确界限）。** 定理 3.4、4.3 不要求 beta；$P$ 可是同一任意合法实际源的到达入口。定理 4.6 若推广到另一个固定客户端，需另证：它的后续原始外部输入均为固定或由实际已有输入计算；完整原始后继能按实际来源分类出所有辅助外部源帧；`00` 后的原始返回及执行前提成立。满足这三项时，上述超前缀归纳仍成立；本文没有为每个 generic 原始客户端建立这三项或其无条件 INITIAL 成功。

证明。前两个定理只使用固定 $P$、七标签 literal reader 和请求保留，与树为 beta 无关。第三个定理的唯一额外输入步骤是最后 `00` 之后不再缺一个变量 IN，唯一额外分类步骤是不会误把 computed command 当外部辅助帧。这两步恰由所列前两项替代，余下确定性归纳及响应证明原样成立；第三项保留实际运行而不凭空假设返回。没有这些项，所用归纳在遇到未给出的 IN 或未分类请求时即无下一步依据。CAP 定义 8.1 明确规定一般 Read/Rho 客户端可用 Append/copy 在 13 上构造与输入帧相同的三块，却不执行对应外部 IN。这是反驳“每个三块都证明一个 `01`”解码规则的实际源文分支；不是反驳所有 generic 客户端的 $Q$ 恢复。ARC 定义 9.4 本来就只给实际提案、先验相容纤维及局部终止等条件下的 generic consumer 保证。$\square$

单次入口的半 ingress、跨调用的封口域和固定 beta 的 INITIAL 域因而分别成立。本文没有把随调用变化的 $P$ 当作免费共同参数，从而将前者偷换成无共同入口的所有半 ingress 定理；也没有把受限 generic 条件称作完整 generic 实例。

## 5. 接回原始 verifier、INITIAL consumer 与价格

**命题 5.1（不更换的消费目标）。** 在定义 4.4 的实际原始停止路径，目标始终是初始源的 $q_{H_0}(u)=q_1(\beta)=(0,B,1)$，即使辅助操作已经改变当前树、当前 $h,K$。沿原始 31→49→21、SEG-P1→50→verifier 32–39、SEG-R1→51→consumer 40–47 的路径，原始 guard、拒绝、binding 检查、目标块 43 的分配和复制、OUT、ACK、token return 以及最后吸收 halt 均保留。本文的恢复定理没有把这些步骤的任何一个换成视图输出。

证明。ARC 定义 9.1 固定的是已经初始化的原始 Stop 提案及 acquired 初始 beta，不是当前树的动态目标。辅助规范调用只用原始 CAP guard 改动当前源和相应日志；原始初始绑定未被改写。ARC 命题 5.5 保持停放客户端，`00` 才按实际贷款进入它。CAP 定义 6.5–6.6 的检查使用原始提案、初始先验、全部实际历史 guard 和 acquired 绑定，ARC 定理 9.2 给出的固定 beta 路径正经这些通道走到真正终端。所有额外规范七标签调用仍由 CAP 的相应原始分支和统一行保留其实际结果，不把拒绝删掉；成立的接受结论仍须这些原始检查及所需局部计算终止。定理 4.6 只识别其已到达的原始切口，不预先代替检查，更不创造新的 posthalt 入口。$\square$

**约定 5.2（联合恢复不是当前可用）。** 定理 3.3 和第 4 节是数学上从完整原始后继恢复联合历史。原始任务把隐藏坐标列入成功响应，不授予 actor 根探测、producer 13/17、latch 或 meter 的当前读权。$A$ 的实际包和此前取得的历史证据也不激活历史 token。若要称一种表示当前可用，必须另给实际 owner route、已取得的目标绑定、有限 codec 和输入/code/scratch 权限、receiver 检查、ACK、mailbox/token return 和每步成本。本文没有这样的新增服务。

**命题 5.3（同一运行计价不变）。** 对本文涉及的任意实际有限前缀，所有原始与新增 native 行都按 ARC 定义 10.1–10.2 计入；仍有 $T_{\rm time}=n,F_{\rm fee}=2n,S_{\rm bits}=S_{\rm irreducible}+b_{\rm ctl}+8A+8n$，$A$ 不含 meter；这些价格坐标与支撑 $S$、发生词 $T$ 类型不同。数学解码器本身没有原生执行价格；一旦实际执行它，其输入取得、扫描、复制、代码、输出、检查和返回必须另计，不得把这些行从 $n$ 中抹掉。

证明。每条实际 native 行贡献一个原始 receipt、一个 tick、两 fee units 及其真实构造；保留的代码、死块、未完成字段和所有复制也在同一链上。ARC 命题 10.3 的逐行求和直接适用。本文仅对同一实际后继作数学函数，没有在机器中增加一步；若增添执行该函数的程序，它的行满足同一计价规则。单列 payload copy/print 的 $\sum_i(17L_i+7)$ 只是既有 subtotal，不能充当整次服务账单。$\square$

## 6. 更广历史选择：直接使用匹配的 GCA 实例

**定义 6.1（匹配实例而非 retrofit）。** GCA 的 $G_{\rm sel}$ 在最初安装时即使用它自己的 $E(L)$、捕获 $101U(\delta_{\rm sel})\Delta(G_{\rm sel})$、$E(G_{\rm sel})$、展开后的 $r_{\rm sel}$ 和 HistoryMode。它不是 ARC 的已运行 $G$ 的免费补丁。参数 $m$ 是实际已取得的旧 CAP unified ordinal，不是 primitive ordinal；$e$ 是该次实际 `01` 分派进入 $F^A$ header/setup 后的 cut，$f$ 是 row ACK/source TOK/最后 idle CTL 后进入 InnerReturn 的 cut。$a,b$ 分别是实际已完成前驱 acquisition 的起止端。

**命题 6.2（已有历史覆盖的准确使用）。** 在这个匹配的 $G_{\rm sel}$ 初始化、到达 Ready 并具备 GCA 要求的实际已完成前驱及 acquired 目标名称时，已有 SourceOffset$(m,t)$ 给出每个实际已返回七标签调用的 $e+t$，$0\le t\le f-e$，包含所有实际返回结果、维护拒绝及 changed idle CTL 后端；已有 AcquisitionOffset$(t)$ 给出该完成前驱的 $a+t$，$0\le t\le b-a$。这不需新增 selector。其交付仍走 receiver 73 的 ClientImage、当前 phase TOK/read、完整 binding 检查、ACK/mailbox return、历史项和 invocation TOK/Ready。

证明。逐项采用 GCA 定义 4.2、5.3–5.6 及其返回定理。上述 $e,f,a,b,m$ 与其定义同名同来源，所以它的旧前驱重建及选取恰落在所列区间；不是把 ARC 的当前调用或别的 $m$ 填进其公式。GCA 第 6 节的实际交付保留所有 acquisition/return 前提，历史 image 中的旧 token 只作数据。SourceOffset 排除 gate 之前和后面的 CaptureCAP；更广 AcquisitionOffset 也要求那个前驱实际已经完成。当前未返回 flight 和最后 `00` 后没有新 Ready 的后缀不满足该入口前提。$\square$

这份能力比 ARC 原先的 strict-Reserve Zero selector 广，不能作为本文新增成果。GCA 命题 3.4 的 mode 0 只保持旧分类及 Zero 意义，不给时钟、地址、capture、完整响应的相等。UAS 的四自然视图及 Cycle 的已支付转换不能因此直接移植到 $G_{\rm sel}$。定理 3.3 的局部 reader 论证可以对它真实匹配的 $F^A$ 重作参数实例，但没有由此建立 $G_{\rm sel}$ 全域的四视图原始 $Q$ 核；GCA 第 9.4 节所留义务仍在。

## 7. 新增输入、changed return 与有偿 native 驱动的界限

**命题 7.1（header/site 保持的恒等输入转接不成立）。** 把实际 history 请求的第三个 `111` header 位直接当作原始七标签源 IN 的同位 Supply，同时保持已消费 header `11`、输入标签和规范任务域，是不可能的。该结论只否定这个保持 site/前缀的转接类别。

证明。$\mathsf C_7$ 的七个源 tag 中，前两位 `11` 只可继续为 `110`，故原始 Supply$(0)$ 可延长，Supply$(1)$ 在原始合法任务域未定义。ARC 定义 5.3 的真实规范 history 请求是 $111U(\ell)U(m)U(z)U(s)$，其第三位必须实际供给 1；它由 70 的不同接收位置取得。恒等转接将这一合法 history 位送到原始任务未定义的位置，不能保持部分映射定义域。原始 raw IN$(1)$ 仍物理执行；把它改称 `none`、或把 history 输入过滤为 0 都不解决该矛盾。非恒等编码、完整协议模拟或其他原始实验需要自己的证明，本命题不排除它们。$\square$

**命题 7.2（逐前缀原始收据刚性）。** 设一个机制从同一个实际原始切口的 $n$ 个 receipts 开始，将每个成功原始 primitive 实验依次解释为 $d_i$ 条真实 native 行，且声称在每个解释前缀结束时完整原始后继、原始 meter 及 receipt 对应均相等。不允许删改这些真实收据，也不引入另一计量链。则每个 $d_i=1$。原始禁用尝试若也保持它未执行的完整响应，就不能解释为任何正数的 native 行。

证明。完成前 $i$ 次原始实验后的要求为 $n+\sum_{j\le i}d_j=n+i$。相邻两个等式相减给 $d_i=1$；$i=1$ 同样成立。原始禁用尝试保持 $n$，而每一实际 native 行添一个 receipt，所以其解释行数只能为零。特别，在第 8 节实际 INITIAL consumer 的一条 EX 前插入 $k>0$ 条 native 检查/驱动行再执行 EX，后继有 $n+k+1$ 个 receipts、额外 $k$ ticks、$2k$ fees 及至少 $8k$ meter bits，不能等于要求的 $n+1$ 收据后继。$\square$

它不要求隐藏 primitive-query schedule 相同，也不否定带一个 staged original receipt 的非 native 细步骤机制。若外层任务仅比较 trace projection 或完成后的抽象状态，可能允许 stutter；但那不是本命题中带实际完整原始 meter 的逐前缀相等。OR 的 completion interpretation 与当前可执行 driver 必须分别承担这一步。

**开放边界 7.3（changed return 不在未变行方块）。** 最后 idle CTL 在旧 raw graph 后继下一帧 IN，在 $F^A$ 后继 InnerReturn。故引理 2.3 的直接对应不能穿过该行；第 3 节删去的正是 next row 为此行的切口。第 4 节重建历史时仍执行这个真实 changed return 及后续额外工作，没有恢复旧快照或擦掉事件。GCA 对其已完成旧发生的取回不自动给当前原始实验桥。为 changed return、gate、history、银行、activation 和其他新增阶段建立原始输入域及完整后继对应仍为 open；这里的 source-grounded 排除不是证明这些阶段不能由任何更合适接口处理。

## 8. 原始 INITIAL consumer 的细切口反例族

**定义 8.1（实际原始行与条件细化）。** 取第 5 节真实 INITIAL consumer 在检查 SEG-R1 和预期 binding 之后，为 task-output 43 做 Zero allocation 的一条普通 EX。它是实际原始非 IN、非 OUT、非 halt 行。现在只作条件命题：假设一个 OR 型细化对这条 EX 有已建立的 continuing authority、before-image 和 head/stage 不变量；每次只 birth 一个顶点，按 parent-first 连接；各取样 cut 的旧顶点和已出生顶点仍形成有限根 child 树；直到独立 Finish 才完成唯一一个原始 receipt，之前不执行下一原始行。没有声称这个细引擎已经实现。

**定义 8.2（细化载体的独立观察）。** 对定义 8.1 的实际细图另记 $S_f$ 为根 child 路径支撑、$B_f$ 为实际 child 终端反链、$T_f$ 为实际细操作发生顺序词。它们按实际关联和发生定义，不按旧任务定义；这些不是宣称 UAS 的原子编码 $U(W)$ 在一个半构造 cut 已经完整成立。若选细 memory，则 $M_{J,f}$ 仍须逐项指定真实 backing、stage 及权利，不能把证明所需的答案塞进选择。

**定理 8.3（49 个 pre-Finish 切口不能由旧 prefix 选择承载）。** 在定义 8.1 的细化中，可选择 49 个 pre-Finish 切口，其 $S_f$、$B_f$、$T_f$ 分别两两不同。任何映到**该同一实际原始运行前缀**、不插入原始行、保持已完成原始 receipt 数的因果解释 $p$，在这些 cut 上均等于原始 EX 前的唯一前缀 $h$。因此这些视图的相等核不等于 $Q\circ p$ 的相等核。即使只要求 $p$ 在该行两个真实端点中选取，仍至少有 25 个上述切口落入一个 $Q\circ p$ 纤维。

证明。UAS 单个原始 cell 的 unary 模板有 23 个顶点，在既有 tail 后 append cell 总共 birth 24 个。所选 EX 构造一个普通 cell，原始 receipt 另外 append 一个 meter cell；OR 第 7.2 节的 $V=24e+s$ 在这里 $e=2,s=0$，所以仅这两次 cell append 就需 48 个 births；细控制器的额外 births 只会增加这个数。取 admission 后的 cut，再取这 48 次 birth 各自之后的 cut。按假设它们都在 Finish 前，原有支撑未删除，每次至少多一个根可达顶点，故所取支撑基数严格递增，至少为 $v_0,v_0+1,\ldots,v_0+48$，两两不同。每个有限根 child 树等于其终端反链的前缀闭包，故 $B_f$ 也两两不同；$T_f$ 保留不同长度的实际 birth 发生，所以同样不同。它们不依赖提前释放输入、输出或终止。

这些 cut 都只有 $h$ 的 $n$ 个已完成原始 receipts。在不插入原始行的同一运行中，该 EX 区间的唯一长度 $n$ 原始前缀就是 $h$；保持已完成 receipt 数迫使 $p$ 恒等于它。因此 $Q(p(x))$ 在 49 个 cut 上恒定，却有上述独立视图区分，二者的核不可能相等。若只保留两个原始端点供选择，至多有两个 $Q$ profile，抽屉原理给至少 $\lceil49/2\rceil=25$ 个在一个纤维，仍非视图核。$\square$

**推论 8.4（细 memory 的条件及 stable 逃逸）。** 若 $M_{J,f}$ 选择实际 birth/stage 信息并能区分上述切口，其核也不能等于这个 $Q\circ p$ 核；若它只保留稳定旧材料，则本定理不声称其有 49 个不同值。OR 命题 5.5 的 stable completion interpretation 不受此反例推翻，因为它只在完成片段的稳定端点定义响应；它也没有据此给出所有细 Busy 切口的原始任务。

证明。第一句只需取两个由所选 memory 区分而 $p$ 相同的 cut；第二句没有该区分前提，不能使用第一句。稳定 completion 不把 49 个 pre-Finish cut 当作 49 个原始端点，其定义域不同，所以不构成本定理的反例。若给 Working 状态添加阶段响应，它可以区分这些 cut，但仍须证明那些响应怎样来自未更换的原始实验，而不能通过改名得到 $Q$。$\square$

parent-first、根可达和保留旧顶点是 49 支撑论证的显式前提。允许 unattached births 的实现不满足该版本，不能冒称已实例化此计数；只要确有两个不同细发生词而仍选择同一已完成原始 prefix，$T_f$ 的核障碍仍成立。此处既不重复 OR 的提前 IN 反例，也不拿 terminal collapse 充当新结果。细机制的结构 tariff 另算；若采用 OR 第 7.2 节的 tariff，$V=48$ 给 $N_*\ge50$、$g_*\ge632+P_*$，而不是把这些细操作当成零价 native 工作。这个条件价不说明机器延时或整次运行最优性。

## 9. raw、终端与所有候选范围的结算

**约定 9.1（保留而未完成的 carrier）。** $\mathcal R$ 仍是 UAS 定义 1.4 的全部实际物理前缀：原始 boot/private acquisition、无效 preparation、错误 bootstrap/raw table、非规范输入、未结束 unary length、frame-fault、部分 loans/copies/banks、暂时无效源和最终 halt 均不删除。本文正定理在 $\mathcal C$ 的所列原始行域上成立，不给整个 $\mathcal R$ 一个输入逆或四视图 $Q$ 等价。无效源覆盖**位于规范调用内**并不因此被删；无效初始化与离开规范前缀的 raw 输入则没有这些正定理的前提。原始合法性检查及所有实际 enabled raw branches 保留。

**约定 9.2（终端与有界历史能力）。** CAP 第 16 节已给同输出不同历史的实际终端族；第 17 节已给最后 Ready/停止后缀界限；第 18 节已给 encompassing-image 资源界。原始空终端响应不含隐藏状态，所以本文不主张在这些终端纤维上恢复历史核。定理 4.6 允许最后**执行 halt 的响应**，但删去终端之间的比较，二者相容。有限实际增长并不产生一条无限物理运行，更不保证暂停输入或局部计算发散时的进度。

**约定 9.3（候选范围逐项承担）。** 下表将提案的范围与本文确实证明的结论分开；各结论以相应正文条件为前提。

| 所提范围或机制 | 保留结果与精确边界 |
| --- | --- |
| 固定实际 reached entry，完整 unchanged source-call body | 定理 3.3–3.4：含 ingress 所有部分状态、七标签全部结果及原始 ACK/source TOK；排除 next changed idle CTL，固定共同 entry 不免费变成任意滚动 entry。 |
| 多次 source flight、postseal | 定理 4.3：固定共同 $P$、此后仅 `01`，封口原始非 IN 行，跨不同已完成调用数；不需容量上界，不含中途 history。 |
| 固定 beta 的 source-only 与原始 INITIAL 后缀 | 定理 4.6：使用实际请求类型/来源及 gate 超前缀，保留完整原始 stopping 路径；不含新增 setup 或终端纤维。 |
| 更广原始源/任意客户端的后缀 | 定理 3.4、4.3 已与 beta 无关；后缀推广仅在命题 4.7 三个实际条件下成立。一般 computed read/rho 的三块反驳纯块计数规则；不据此否定一切 generic 恢复。 |
| 历史 `111` 与七标签源 parser 恒等转接 | 命题 7.1 精确否定保持 header/site 的恒等转接，不否定所有编码协议；新增输入域桥仍 open。 |
| 额外 native driver 后忽略其 meter | 命题 7.2 否定完整后继逐前缀相等；非 native staged receipt 不在这一反证类中，仍须源/权限实现。 |
| 将全部 exposed fine cut 选成旧原始前缀/端点 | 定理 8.3 在实际 consumer EX 的显式细化前提下否定；不否定 stable completion，也不宣称已实现细引擎。 |
| 扩大已返回历史目标服务 | 第 6 节直接复用匹配初始化的 GCA；不再实现 selector，不把它当 UAS/Cycle 共用实例或当前 Busy 权限。 |

## 10. 未被局部正结果替换的完整目标

**开放问题 10.1（原始实验桥）。** 仍须为原始 $Q$ 给出所有新增 gate/history、activation、bootstrap、银行、parser/package/invocation、InnerReturn/CaptureCAP 和 changed return 的实际实验域、标签、输出及完整原始后继对应；同时处理跨本文 chart、raw、preacquisition、非规范、未完成调用及终端的适当结论。已有历史等价、$Q_G$ 或一个新 Working 任务不能代替这一步。本文不声称 restricted charts 的并已经是全域。

**开放问题 10.2（实际原始行实现）。** 完整原始行的 source-correct raw decoder/checker、有限控制与一次实际初始化、当前持续权限、两个 meter 头及 alias、accepted IN/OUT 的原始时序、所有 receipt/return 和吸收 halt 仍是独立未履行义务。未提供的行引擎不作为本卷 primitive。这里在已规定 CAP/ARC 源语义上的普通证明，不补出该实现。

**开放问题 10.3（细 cut 与当前使用）。** 须实际建立 before-image、head/stage、非 child incidences、pending event 与 staged receipt 的不变量，补全 OR 对全部原始行/协议的 completion 前提，并给细 Busy 的未换任务接口。当前合法取得还需目标 binding、有限 codec、实际输入/code/scratch 访问、receiver/check/ACK/token/return 及完整同运行成本。联合数学逆、历史 image 和付了某 tariff 都不单独授予这些权利。

**开放问题 10.4（全程序的保留要求）。** 原目标仍是一个有限初始化的共同源装置，在真实任意有限未来增长中使独立空间/过程/边界/保留记忆在所需范围互相恢复并能合法使用，保留原始 verifier/INITIAL、全部源结果/guards/releases、所有回执与终端输出。匹配 $G_{\rm sel}$ 的历史覆盖不解决它与 UAS 四表达共用实例的问题；最后没有后续 Ready 的 suffix 也无免费历史入口。更广晚目标的 $M_1(D)$、sharp $\lambda$、全尺寸有效认证、最简性、物理符合性、最优资源和无界持续进展均未由本文证明。上述 open 不免除原目标的任何要求。

## 11. 复用、成熟方法与适用界限

**约定 11.1（固定仓内来源）。** 下表均取同一源快照 `db2225af354815a069ce1daa607706f3a9ded2fa`。这些是来源地址。

| 简称及来源 | 本卷使用、既有重叠及不承担部分 |
| --- | --- |
| [AIF](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md) 2.2–2.6、4.4 | 原始实际输入、部分任务和确定性回放；不新增 replay 定理。 |
| [SSA](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md) 4.4、7.2、12.1 | 已有固定容量自然视图/原任务核，作为已覆盖范围，不重做。 |
| [CAP](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md) 4.6–4.7、6.1–6.7、7.4、8.1、12.2 | literal reader、保留描述符/请求行、原始消费及实际来源分类；借用 replay/superprefix，不借文献或解释授予权限。第 13、16–18 节的 old-memory、终端、horizon、资源界均直接复用。 |
| [ARC](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md) 4.1、5.2–5.5、6.1–6.5、9–11 | 实际 source inlining、gate、返回、输入 reservoir、固定 beta 初始化/consumer 及价格；最后 changed CTL 不冒充未变。 |
| [UAS](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GROWING_UNARY_STORAGE_ATLAS.md) 1.4、2、3.1–3.5、6.2–6.4 | 已有独立自然表达、raw 逆、规范历史核和 strict-Reserve Zero 原任务核；本文新增的是 Zero 之外具体源调用的旧坐标输入/原始后继桥，不将这些旧核计作新增。 |
| [Cycle](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GROWING_PAID_VIEW_CYCLE.md) 7.4、9.2 | 已有 acquired strict-Zero 转换及 receiver/cost；不借它产生任意 fine-cut codec。 |
| [OR](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OPEN_ROW_COMPLETION_AND_AUTHORITY.md) 4、5.5、6.1–6.2、7.2 | before-image/权限/收据条件、stable completion、条件 fine-history、真实 INITIAL consumer 与 birth 计数；均保留尚未实例化的全行条件。 |
| [GCA](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_CUT_ACQUISITION.md) 2–6、8.3、9.4 | 已有更广历史 selector 和真实交付；精确参数/初始化见第 6 节，不重新实现，不暗移四视图核。 |

**约定 11.2（D5 与 Scribe 引文）。** `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean` 的 `nativeStep`、`Replay`、`replay_deterministic`、`reached_prefix_replay`、`actual_register_execution` 给原始串行语义和回放；`NativeFullSourceProducer.lean` 的私有 `traverse`、`production_reads`、`stationary` 及公有 `native_source_producer` 给实际完整源取得，不能直接充当 CAP 的 native 权限/价格实现。`NativeSerialEffective.lean` 的 `original_code_service_simulation` 和 `terminalObservation` 使用自己的代码实现和外部 trace 终端读数，不与这里的空终端响应混同。`D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean` 与 `PredictiveMemoryMinimalQuotient.lean` 给带明确 readout/update 前提的抽象核，不能补出 concrete 输入域。

相关叙述见对应 `Blueprint/D5/` 镜像的同名 `.scribe.cs`。上述引用不直接提供这里的匹配 WR/跨辅助调用输入对应；这不是全库不存在性声明。

**约定 11.3（外部主源与文献状态）。** 下列成熟方法只承担其明确内容；没有把一个仿真定理的名称当作本装置的权限、初始化或实验桥。

| 主源 | 确切用途与文献状态 |
| --- | --- |
| [mathlib `StateTransition.lean`](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/StateTransition.lean)，固定版本的 `Respects`、`tr_reaches₁`、`tr_reaches` | `literature-attested`：匹配关系和非空目标片段是显式前提，原始 `none` 需相应终止条件；不能把 task-undefined raw Supply 塞成 `none`。 |
| [CompCert v3.16 `common/Smallstep.v`](https://raw.githubusercontent.com/AbsInt/CompCert/v3.16/common/Smallstep.v)，`fsim_properties` | `literature-attested`：初态、终态、相同 trace 的有限片段和良基 stuttering 条件；不推出含实际 meter 的完整后继相等，不授予 actor 访问。 |
| [Lynch–Vaandrager, *Forward and Backward Simulations*, Part I](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf)，§3.2、Lemma 3.8、Theorem 3.10 | `literature-attested`：前向模拟经有限执行片段给 trace inclusion；不是四独立视图、原任务逆或当前 driver 的构造。 |
| 本卷第 3–4、7–8 节的具体源对应及边界 | `repo-derived`：在上述源文模型中的普通推导。匹配 WR、gate 输入冗余、原始 consumer 的细 cut 计数是具体应用；不作 `suspected-novel` 或全球新颖性声明。 |

**约定 11.4（适用范围与可反驳判据）。** 有限读入骨架只能检验指定输入上的匹配写入规则，不能替代源服务、完整描述符、信道和实际 whole-run meter。

一个实际反证器可针对定理 3.3 寻找同固定 $e_P$、相同原始 13/latch 5/meter 而不同实际前缀的两切口；或者指出一次 IN 后、匹配 WR 前真实覆写 latch 5 的原始行。针对定理 4.6，可给出固定 Stop 路径上的额外独立 IN、原始请求来源不能区分的两个实际列表，或其 gate 超前缀在停止点前消费了错误位。针对定理 8.3，应在候选实现中标出那 48 次真实模板 birth，逐个检查取样 cut 的根可达支撑、已完成原始 receipt 数和所选原始 prefix；少一个模板 birth、一个 cut 丢失旧顶点、在 Finish 前已有额外完整原始 receipt，都会使它不满足所用前提。保持全部前提而又为这 49 个 cut 构造核相等的原始端点选择，才构成该条件结论的反证。这里不以未发现这些反证当作原生实现或全目标证书。

## 追加锚（本行以下为增补区）
