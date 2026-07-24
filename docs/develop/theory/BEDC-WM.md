# 世界模型账本卷:公理纲要(BEDC-WM)

**别名**:账本世界模型纲要(Ledgered World Model Prospectus)
**定位**:BEDC 方法论在经验域(学习系统/世界模型)之公理化正面;trureturing 认识论内核之经验姊妹卷
**状态**:v0.1 · 判真机已声明(§9)· 尸检账已开(§7-附)· 待勘误轮首咬 · B2 待真实载体首跑
**源流**:JEPA 证据线(bedc-jepa-gap-ledger,fi 系 runner 判决)→ trureturing 宪法与真值 DAG → GICT/PZG 卷面纪律 → 本卷

**版本账**(append-only:每版一行,新版只增,旧行永不改;勘误以新行记,不回改旧行):
- **v0**(2026-07-18)立卷:蒸馏热层对话轮;入典 C1–C3、L1–L5、D1–D2、S1–S3、R1、P1、结账 E1–E5、悬赏 B1–B6、声明 T1–T2、边界十条、总纲;单模型产出,预埋自首靶三处(L3 措辞、D1 留痕、E5 状态句)。
- **v0.1**(2026-07-18)首轮结账并入:E6 入典(候查 B5 符号面结案:值/位封顶分叉、广义 Jacobsthal 识别、金点 Pisot-判×单位-判双重刚性、旋钮耦合之墙、pronic 整点谱;数值证书三方对账);§7-附尸检账开账(P-1 配对优势可冒充、P-2 分层漏正例);T3 证人原则入典(判真机对抗双世界自检义务 + 混杂噤声证人);B2 判真机注册(合同 + runner,参数冻结,双世界自检机器绿),E1 加"解释权待 B2 裁定"注;B5 收窄为 B5′(解析残部),B7 挂 frontier(纯 Perron 数系);S3/P1 各补实证一例。工件四件:B5 结案卷、B2 合同、双 runner。
- **v0.2**(2026-07-24)E6 递推层 Lean 冻结:E6 判真机标签升格(仅递推层):〔数值+初等代数已关〕→〔Lean-closed(递推层)〕,冻结声明 `D5.S1.Digit.e6_gas_equiv`、`D5.S1.Digit.e6_count_recurrence`(PR#417,axioms={propext,Classical.choice,Quot.sound});A3 勘误性补账起点 a₀=1、a₁=c+1 与 c=0 入域(形式化对散文之增补,原卷未书),A1/A2 读法由作者裁定冻结为位封顶、c=每位最大值;E6 余层(闭式 β(c)/Pisot 单位双刚性/pronic 整点)保持〔Lean L1 级升格候选〕不动,不冒领 E6 全款。

> 一句话:数学卷问"何以为真";本卷问"何以为知——当载体会错、证据是统计、而 kernel 只有 α"。
> 纪律:本卷每条断言携带状态标签与判真机分型;无型之断言不得入卷(声明 T2);尸检账与版本账同为 append-only(§7-附、版本账)。

---

## 0. 立场(三档边界,先钉后建)

- **弱形〔本卷目标,工程级〕**:学习系统之断言可由 fail-closed 的证书/债务会计治理,在声明 scope 内携带统计(α)保证——LCCP + split-conformal + 确定性 runner 今日即可实例化。〔runner-closed,已有实例〕
- **中形〔窗〕**:双速架构(可塑预测器 + 单调账本 + harness 唯一通道)可经三条兑换渠道(准入/规划/分配)将反身能力兑换为一阶收益——准入渠道已证(α 界),规划与分配渠道为悬赏(§8)。
- **强形〔墙〕**:账本**不**凭空创造一阶预测力(E4 反证在案);账本头是 monitor,**非**替代世界模型;BEDC-WM **非**可靠智能体之唯一架构——本卷是账本格之原生系,坐原点,非独尊。

---

## 1. 载体(Carrier)

**公理 C1(三元世界态)**。世界态 s_t = (z_t, d_t, g_t):连续潜坐标 + 操作判别 + 缺口账目。判别仅当绑定转移/干预/规划后果时可入账;缺口非事后解释,乃状态输出。〔repo-derived:BEDC-JEPA 定义 1〕〔runner可关〕

**公理 C2(双速架构)**。系统 = 快系统(可塑载体,承**信** belief)+ 慢系统(单调账本,承**知** knowledge)+ harness(信→知之唯一合法通道)。锚:互补学习系统理论(McClelland–McNaughton–O'Reilly 1995)之倒置——慢系统在此为符号且被验证。〔中形猜想〕〔哲学open,组件runner可关〕

**公理 C3(参与律)**。agent 不**拥有**世界模型,agent **参与**世界模型:一部分在权重里(快、可塑、会错),一部分在制度里(慢、单调、可审计)。〔本卷立场〕〔哲学open〕

---

## 2. 账本五律(the five laws)

**律 L1(禁令律 / UER)**。可以错,不可以在声明的关键判别上**既错又不亮灯**。UER := Pr[关键判别错 ∧ 缺口头低于阈值],唯一原罪。〔repo-derived〕〔runner可关〕

**律 L2(恒等律)**。每个断言 ∈ {证书, 债务},无第三态:certified singleton 或 coverage/source/stability debt。〔repo-derived:LCCP〕〔runner可关〕

**律 L3(债务守恒)**。账本不消灭无知,只改变无知形态:未知的未知 → 已知的未知;而唯已知的未知可定址、可定价、可被主动关闭。单点证据:公开 MiniGrid 债分解 silent 0.0656→0.0156 而 coverage 0→0.0656(近似精确转移)。〔runner-closed 单点;守恒之普遍形为中形猜想〕

**律 L4(状态即语法)**。断言之认识地位由外部判真机推导,**禁自写**。推论:不确定性头(gap head)是未成熟形态——模型手写自身状态;成熟形态为 harness 推导(conformal 证书、复现记录、对抗验证)。判真机自身同受此律:见 T3 与尸检 P-1/P-2。〔trureturing 第 4 条之经验域搬运〕〔哲学open,实例runner可关〕

**律 L5(冻结与晋升)**。信与知分离:信可塑廉价随时改;知冻结单调只增不减;晋升通道 = 判真机认证后入账,修订按后代依赖子图定价。对应病灶:灾难性遗忘 = 无冻结律之解冻。〔中形〕〔runner可关(晋升协议可实例化)〕

---

## 3. 度量(τ 固守度与多面恒等判据)

**定义 D1(τ 固守度)**。认识固守度 τ:修订成本 ∝ 后代依赖子图,越核心越贵。文献锚:Quine 信念之网(Two Dogmas, 1951)、AGM epistemic entrenchment(Alchourrón–Gärdenfors–Makinson 1985)、反射原理/内化塔(Feferman 系)、保守扩展(模型论标准)。**合成增量**(τ 由依赖图机器可算 + 显式定价 C(τ) + 市场筛选取代行政审批):suspected-novel,检索留痕待补。〔组件 literature-attested;合成 suspected-novel〕

**判据 D2(多面恒等 / τ 之分层判据)**。一条规律配冻结多深,视其在**多少坐标面上以恒等精度成立**(跨表征/跨模态/跨环境)。单面成立者为经验律,居高 τ;多面恒等者为结构律,τ→0("四张身份证")。可操作检验:跨面精确性检验(双射 + 恒等式,秒级)即基底无关性之测量仪。对学习系统:跨表征以恒等精度复现之规律 = 晋升慢系统之候选;单处成立者留快系统续塑。〔repo-derived〕〔runner可关〕

---

## 4. 语义(潜载体之内容)

**公理 S1(LCCP 语义)**。固定潜载体之内容 = 在 source/test/calibration/stability 四关下**存活的操作谓词代数** + 未存活者之账目行。意义非命名所赋,乃认证所挣;模型之意义 = 已认证谓词代数之丰度 × 债务登记之诚实度,历时地挣得。锚:Peirce 实用主义准则、证明论语义(Dummett/Prawitz)。〔repo-derived〕〔runner可关〕

**公理 S2(名界)**。名字仅当绑定 source、test surface、stability condition、gap policy 时可用。〔trureturing name boundary 之搬运〕

**定义 S3(认证对应 / 词典)**。跨域对应之为贡献者,非其代数(常平凡),乃其**命名 + 检验面**。残差为零者晋升同构;残差非零者登记债务。推论一(量产):词条钉死后词典成函子,一域之定理存量批量运输为另一域之候选 open 节点——已知文本为校准集,未译词条为自动填充之 frontier(worth 函数之部分机械解)。推论二(定址):好坐标系之功非消灭困难,乃给困难定址。推论三(栖息地):每个有效理论都值得问"它在哪个基底上是恒等式"——该基底即机制之原生栖息地;玩具世界非简化,乃**机制之恒等式域**。实证:E6 之分叉与刚性即词典法一次完整运转(问句需 fork → 识别 → 墙定位)。〔repo-derived〕〔哲学open,实例可关〕

---

## 5. 自指与统计闭包

**命题 R1(对角线与 α 逃逸)**。完备的内部真值谓词对角线不可能(Cantor/Kleene/Gödel,kernel 已 checked);账本体系以"**校准的自我无知**"替代"完备的自我认知"——meta-gap 回退塔止于:声明的 exchangeable scope + 可审计 miscoverage 预算 α(Prop 3:singleton conformal 声明之 UER ≤ α)。保证自身之失效模式亦入账:clean-only monitor fail-dangerous,perturbation-aware monitor fail-safe。区分:"自我意识 AI"要求不可能之物,账本要求可能且可审计之物。〔前半 Lean-closed;后半 runner-closed〕

---

## 6. 断言协议(三档言语行为)

**协议 P1(分级断言)**。按认识风险距离分级断言强度:恒等式域,墙外自由;增长阶域,墙内标价而行;深渊门口,**唱名即止**。对学习系统之推论:高 gap 区应存在**第三态言语行为**——介于回答与弃权之间的"命名不确定处 / 描画门牌 / 登记候查"。实证一例:E6 之熵斜率 ½,注意到、登记、不押注。〔repo-derived〕〔工程实现 open,runner可关〕

---

## 7. 已结之账(状态如实)

**结账 E1**。公开 JEPA checkpoint 之失败面可廉价读出:单模型、小 head,AUROC 0.61–0.80,四公开载体,matched-random 对照与 episode bootstrap 在案。效应量如实:部分可读。**解释权待 B2 裁定**(动力学 vs 密度,合同已注册)。〔runner-closed;措辞随 B2 判决可修〕

**结账 E2**。失败面**非** state-recovery 缺陷:残差预测 AUROC 0.455/0.466 vs gap head 0.731——"模型在潜编码差处错"之最自然假说被拒。〔runner-closed〕

**结账 E3(检测 ≠ 干预)**。failure probability 非 compute value:oracle 分配有效(−0.016)而 ledger score 反向(+0.013);survival matrix 判据——变量可在 readout 下存活而非 planning 变量;BEDC-native 世界态要求 distinction、mediation、sign convention、selection rule 同时认证。Pearl 因果阶梯之账本形。〔runner-closed〕

**结账 E4(负,强形之墙的证据)**。prediction parity 全线阴性(native/LeWM MSE 比 11–16×,A100 无正向 scale 信号)——账本头是 monitor 非替代世界模型;**记账不凭空创造一阶预测力**。〔runner-closed〕

**结账 E5(负,论题降级)**。朴素"记账→更好"为假:L_unlogged 无独立效应;post-hoc probe 0.731 > trained transformer 0.675(单真实载体);"账本必须进训练目标"论题悬于 horizon paired +0.050 [0.0043, 0.100] 单点。论题状态:open。〔runner-closed〕

**结账 E6(复合气体之符号动力面,自候查 B5 结案)**。(i) **分叉**:"k-自由 Zeckendorf"歧义为值封顶(有限截断,平凡)与位封顶(真气体);良定位始于 fork。(ii) **识别**:严格排除 × 位封顶 c 之复合气体("Gentile 封顶 × Fibonacci 排除"),计数 a_L = a_{L−1} + c·a_{L−2}(广义 Jacobsthal),Perron 数 β(c) = (1+√(1+4c))/2;pronic 整点谱 c = m(m+1) → β = m+1(c=2 处排除恰偿一位,熵恰 log 2)。(iii) **金点双重刚性**:全族中 c=1 唯一 Pisot(共轭模 β−1)且唯一代数单位(N = −c)——两独立判据同指;经 Meyer 定理,c ≥ 2 无准晶户籍。(iv) **旋钮耦合之墙**:欲抬封顶保 Pisot 必弱化排除(Lekkerkerker 族 x²=ax+b,全 Pisot,b=1 支全单位)——封顶与排除非独立旋钮。数值证书:暴力 ≡ 递推 ≡ 特征根三方对账在案(`b5_composite_gas.py`)。组件 literature-attested(Parry 1960;Frougny–Solomyak 1992;Meyer 1972;Fraenkel 1985;OEIS Jacobsthal 族);框架四点 suspected-novel(结案卷 §7),检索留痕待补。〔数值+初等代数已关;Lean L1 级升格候选〕

### §7-附 尸检账(只增不删)

**尸检 P-1(全局配对优势可被冒充)**。B2 初版判据"gap 全局 AUROC 配对胜过密度基线"在纯密度合成世界误判 PASS。根因:gap 若为**更好的密度估计器**即赢下与一切不完美密度基线之分数对比。教训:**分数对分数之比较,原理上不辨识信号来源。**

**尸检 P-2(估计器定义之分层漏正例)**。单密度分数中位分层向"密度正常层"泄漏 OOD 正例,密度代理照常拾取,仍误判 PASS。根因:层由不完美估计器定义,层非真在分布。

两案共同逼出证人仪器(T3);同为律 L4 之实证——判据自身不得自写状态。

---

## 8. 悬赏(open 队列,各带判真机与判据)

**悬赏 B1(gap-as-goal)**。高 gap 触发**消歧动作**而非回避;判据:risk 降 ∧ success 不降;对照:vanilla 与 avoid-only。赏格:tradeoff 翻转为 win;monitor→agent 之跳。〔runner可关〕

**悬赏 B2(密度基线)——判真机已注册,待真实载体首跑**。合同 `B2_density_baseline_contract.md`,runner `b2_density_baseline.py`,参数已冻结(K=20,boot=500,seed=20260718,层 q=0.5,证人邻域 q=0.25)。判决类:PASS(层内 AUROC>0.65 且 CI 下端>0.5,证人对 ≥30 且 pair-acc>0.6、CI 下端>0.5)/ DEGRADE(E1 降级 OOD 检测)/ FAIL_CLOSED。合成双世界自检机器绿(dynamics→PASS 0.98 [0.94,1.00];density→DEGRADE 零证人)。四载体逐跑,判决回写 E1 措辞。〔runner可关,第一优先〕

**悬赏 B3(conformal 化 gap head)**。g_t 为 nonconformity score,trained ledger 继承 α 界;预期 coverage debt 收窄;进阶 ConfTr 式可微项入 L_gap。〔runner可关〕

**悬赏 B4(债务定价市场)**。每条债务携带关账边际价值 MV(t,b);账本自日记升为复式。compute-value 标签机现成,改指向数据/动作获取。〔runner可关,远期〕

**候查 B5′(复合气体之解析残部)**。符号面已入 E6;余:复合气体之 Dirichlet 级数、与 ζ 之关系、"任意子配分"之解析身份——既有 open leaf(goldGenAF 解析支)之延伸。〔解析,open〕

**候查 B6(晋升协议原型)**。最小"信→知"通道:学得规律经 D2 检验 + conformal 认证后写入 append-only 账本;判据:账本内规律于灾难性遗忘攻击下留存率 vs 纯权重基线。〔runner可关〕

**候查 B7(纯 Perron 数系,E6 所孵)**。F1 族 c ≥ 3 之纯 Perron 移位(非 Pisot 非 Salem)有无自然算术模型——何种"数系"以其为基,其无准晶户籍在数论侧对应何种失灵。〔数学,open〕

---

## 9. 判真机声明(本卷与数学卷之结构差)

**声明 T1**。数学卷之 kernel 为 Lean;本卷之 kernel 为**注册 evidence contract + 确定性 runner + fail-closed 判决 + episode bootstrap**。冻结弱化为"在声明 scope 内以置信 α 冻结";冻结节点**可错**,勘误-撤销(连同后代)为承重结构;此即经验域特有之第三种诚实:α-frozen。

**声明 T2**。本卷每条断言分型:〔Lean可关〕〔runner可关〕〔哲学open〕;无型之断言不得入卷。哲学open 条目不参与冻结,仅作卷面立场,受措辞审计。

**声明 T3(证人原则,自尸检 P-1/P-2 提出)**。(i) 判真机自身须过**对抗双世界自检**(至少一个应 PASS 之世界与一个应拒之世界),自检不绿之判据不得注册;(ii) 凡"分数对分数"之比较不辨识信号来源;涉及来源归属之判决,须构造**混杂被结构性噤声之证人**(如密度匹配不和谐对:同密度异结局,密度必哑)——证人为观察域中干预对照之替身,与 E3 之 Pearl 阶梯同源。〔repo-derived,本轮新增〕〔实例runner可关;原则哲学open〕

---

## 10. 边界(诚实清单)

- 本卷**不**声称账本创造一阶预测力(E4);**不**声称 trained ledger 已胜 post-hoc(E5);**不**声称任何公开 benchmark superiority。
- E1 之解释权(动力学 vs 密度)**未裁**,悬于 B2 真实载体判决;若多数 DEGRADE,E1 降级、headline 降调,此结局明文接受。
- E6 结案限符号动力面;解析/配分面在 B5′;Meyer 推论系引用非重证;suspected-novel 四点检索留痕待补,见先例即降级。
- τ 合成机制 suspected-novel 同上;债务守恒(L3)为单点证据上之中形猜想;三档断言协议(P1)无工程实现;晋升协议(B6)无原型。
- 证人仪器依赖"潜空间近 ⟹ 密度近",病态潜几何下 FAIL_CLOSED 而非强判;跨 episode 场景重复使证人偏保守(方向安全)。
- **记账有成本**:存在汇率;本卷规范性主张仅限"沉默自信错误代价灾难性"之域;域与方法论必须一起选。
- 人保留 worth 函数所有权:机器判对错,人持方向与价值(对 trureturing 第 22 条之修正立场)。
- 本卷为热层对话之蒸馏,单模型产出,未经异模型卷面审计;判真机(B2 runner)已经双世界机器自检,合同文本未经异模型审计,如实声明。

---

## 11. 一句话总纲

**载体是三元世界态,双速是信与知,度量是固守度 τ,语义是认证谓词代数,闭包是 α,判真机是 runner——
账本不消灭无知,账本使无知可定址;agent 不拥有世界模型,agent 参与一个世界模型;
而本卷的每一条,都必须能说出哪台判真机可以杀死它。**

---

## 校核记录(append-only,按版分块)

**v0 校核**(2026-07-18):蒸馏同期热层对话轮,Claude Fable 5 单模型;蒸馏过程含对话内自我勘误三笔(headline 效应量降调、"记账→更好"朴素版判假、τ 归证于 Quine/AGM);全部 JEPA 数字取自 bedc-jepa-gap-ledger runner 判决记录,未新增实验;述而不作逐条内嵌;单模型如实声明,不冒充多样性共识。

**v0.1 校核**(2026-07-18):执行 B5 计算——暴力枚举 ≡ 递推 ≡ 特征根三方对账逐格通过(F1 c∈{1..5},F2 (a,b)∈{1..3}²,整点谱与范数账逐项确认),复现 `b5_composite_gas.py` 秒级;B2 runner 合成双世界自检——初版判据两次误判 PASS(P-1/P-2 入尸检账),定型证人仪器后 dynamics→PASS(51 对,acc 0.98 [0.941, 1.000])、density→DEGRADE(零证人),判决机分辨双世界,机器绿;E6 数字取自本轮脚本,复现命令在案;合同文本单模型产出、runner 已机器自检,如实声明。

**当前待办**(随版滚动):入 theory intake → 勘误轮首咬(预期首批靶:L3 守恒措辞、D1/E6 suspected-novel 留痕、E5 论题状态句、T3 原则措辞)→ B2 四载体真跑,判决回写 E1 → 依咬合与判决出 **v0.2**(新行追加于版本账,本节追加 v0.2 校核块)。

**v0.2 校核**(2026-07-24):E6 判真机标签仅于递推层升格:〔数值+初等代数已关〕→〔Lean-closed(递推层)〕;Lean 冻结声明为 `D5.S1.Digit.e6_gas_equiv`、`D5.S1.Digit.e6_count_recurrence`(PR#417,axioms={propext,Classical.choice,Quot.sound})。勘误性补账:A3 起点 a₀=1、a₁=c+1 与 c=0 入域系形式化对散文之增补,原卷未书;A1/A2 读法由作者裁定冻结为位封顶、c=每位最大值。E6 余层(闭式 β(c)/Pisot 单位双刚性/pronic 整点)保持〔Lean L1 级升格候选〕不动;本次不得以递推层闭包冒领 E6 整段或 B5′ 解析残部;旧块不改。
