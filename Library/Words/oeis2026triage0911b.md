---
bibkey: oeis2026triage0911b
authors: OEIS Foundation Inc.; Codex triage workers
year: 2026
title: Fourth OEIS proof triage — finite decision sampling, 0911b
doi: null
url: https://oeis.org/
claim: Source-based triage only; no new mathematical theorem or Lean module is claimed.
strata_touched: []
license: citation-only
triage: anchor
---

# 第四轮 OEIS 分诊：判据不变，采样偏向第一档

**落盘纪律：每分诊完一批就 git commit + git push。** 本文件逐批增长，每批完成即推送指定分支；最终计数以收尾版为准。

基线 `0df1fdcb348147a3ebaea8a607db3662f07cb35e`（开工时 `origin/dev` 与远端 dev 一致），分支 `lane/math/oeis-triage4-0911`。Mathlib 钉版 `db584cd6d46c92f209a44c0f1c829460d327499d`，Lean v4.33.0。日期标签0911b沿用brief；实际采集日为2026-09-10（Asia/Singapore）。产地：Codex 主循环与三个同模型族 codex-cli 全条目阅读席；主循环综合、核对关键声明及数值，不冒充异模型独立共识。lean4 skill 仅用于只读声明检索，无Lean编译或内核重验。

## 判据、预算与统计口径

第一档靶的判据是「该陈述在文献中有没有证明」，不是「有没有人写过」。档位与前三轮相同：1为可考虑短组合/算术逃逸的小猜想，2为非常规有限计算前沿，3为尚无短逃逸的核心问题，out为已知、错误、纯定义或不派的渐近/分布目标。`published` 表示精确目标有公开证明或反驳（公开仓内证明另注明），出现过猜想不算证明；`open` 只限所读材料仍作猜想且未找到证明；`unknown` 为定义桥或证明身份未核实。数值yes仅指可作有意义的有限检验。bind-only风险是具名声明与目标比较，不用“mathlib里还没有”冒充开放性。

本轮预定预算为30条计入分母的候选，按完整评注中的奇偶、剩余、分类、恒等式、计数形态优先采集；第三档只登记note-only，另计且不占预算。第一档占比争取超过40%，不是必须凑出的配额。校准仍是A392698“写过猜想”不足以降级，以及A388724的真实期刊证明足以降级；两条均为brief的历史判例，不重复计入本轮。

当前批次已完成12条（预算30）；完整收尾统计将在其余批次完成后写入。

## 来源与完整性

官方镜像为 https://github.com/oeis/oeisdata ，本次 `git ls-remote` 实测HEAD仍为 `69b127f67c75990effad199e316d6e8a5183b64c`。发现窗为该快照的A390000–A399693十个目录；复用第三轮留存的完整镜像快照作发现和阅读，缺文件才按此SHA补取原始`.seq`。关键词粗筛只用于发现，不据局部摘录作裁决。前三轮表格复原出372个唯一排除A号；新预算与note集合均与其零交集。

来源如实分列：**镜像原文不冒充OEIS接口响应**。本轮对 `https://oeis.org/search?q=id:A397588&fmt=json` 实际取得HTTP200的完整原始JSON，并完整阅读；其余条目来源逐项见attempt里的`manifest.json`。不能把前轮HTTP429冒充本轮读数。

本体及comment/formula/xref的所有直接A号均取完整条目；不递归无限追引。每段末列全部直接A号，同族说明合几席及原因。完整字段与外链全文是两笔账：条目读全不代表外链已读；来源原文、数值脚本与读取清单在runner attempt中保留，永久公共入口为钉版镜像URL。

## 未主张栏

未主张检索穷尽；未主张 `open` 等于全球无人证明；未主张外链论文已全文审读；未主张 `published` 等于原猜想为真。凡未真正打开的页面一律 **ASSUMED-UNVERIFIED**，逐段点名的打开页与源文件才承重。未运行Lean，未主张新定理、冻结、CI通过或已经合并。有限前缀和数值拟合不提升为全称证明。

## 排序表（计入采集预算）

| A号 | 一句话陈述 | 档位(1/2/3/out) | 文献(open/published/unknown) | bind-only(low/med/high) | 数值可验(yes/no) | 建议(dispatch/note-only/drop) |
| --- | --- | --- | --- | --- | --- | --- |
| [A397588](https://oeis.org/A397588) | a(1)=1、a(n)=(n+1)Σa(k)a(n−k)的奇项指标恰为2的幂。 | out | published | high | yes | drop |
| [A397265](https://oeis.org/A397265) | ∀n≥1，r₂(n,1)=A007808(n)−n!；r₂计数n个有标号对象的有序划分且恰一个大小≥2的块。 | out | published | high | yes | drop |
| [A396093](https://oeis.org/A396093) | B(x)=x/(1−x)²，a(n)=[x^n]B(B(B(x)))；∀n≥1，a(2n) 偶，且 a(2n−1) 偶 ⇔ ∃k≥1,n=5k−2。 | out | published | high | yes | drop |
| [A397347](https://oeis.org/A397347) | 对数系数a(n)模4为[1,3,3,3]周期；已由邻序列的更强归一化模8定理覆盖。 | out | published | high | yes | drop |
| [A397902](https://oeis.org/A397902) | A∈xℤ[[x]]，∀m>1，[x^(m−1)](1−A)^(m²)/(1−m²x)=0；∀n>2，a(n)奇⇔∃k>1，n∈{2^k,2^k−1,2^k−2,2^k−3}。 | 1 | unknown | med | yes | note-only |
| [A397594](https://oeis.org/A397594) | A_y(0)=1，∀m≥1，[x^(m−1)]A_y(x)^m/(1−mx)=(ym)^(m−1)，y=4；∀n>3，a_y(n)奇⇔∃k>1，n=2^k±1。 | 1 | unknown | high | yes | note-only |
| [A397592](https://oeis.org/A397592) | A_y(0)=1，∀m≥1，[x^(m−1)]A_y(x)^m/(1−mx)=(ym)^(m−1)，y=2；∀n>3，a_y(n)奇⇔∃k>1，n=2^k±1。 | 1 | unknown | high | yes | note-only |
| [A396491](https://oeis.org/A396491) | ∀n≥1，n 个有标号变量、允许子句内重复文字及公式内重复子句的五子句 3-SAT 不可满足公式数，等于 %F 给定的十项二项式多项式。 | 1 | unknown | med | yes | note-only |
| [A396354](https://oeis.org/A396354) | ∀n≥1，四子句多重集 3-SAT 的不可满足公式计数 a(n)=n(16n^6+48n^5+340n^4+180n^3+2818n²−10011n+6789)/18。 | out | unknown | med | yes | note-only |
| [A395896](https://oeis.org/A395896) | ∀n∈ℕ，n 偶数 ⇒ ∣{k∈ℕ:1≤k<m², rad(k)∣m, rad(k+1)∣m}∣=0，其中 m=A019565(n)。 | out | published | high | yes | drop |
| [A395754](https://oeis.org/A395754) | ∀n≥1，令 m=A005117(n)，m 为奇数 ⇒ a(n)=0；a(n)=∣K_m∣，K_m={k∈ℕ:1≤k<m²,rad(k)∣m,rad(k+1)∣m}。 | out | published | high | yes | drop |
| [A395721](https://oeis.org/A395721) | ∀n≥1，令 m=A005117(n)，a(n)=max K_m（K_m为空时取−1）；猜想 m 奇数 ⇒ a(n)=−1。 | out | published | high | yes | drop |

## 逐条证据

### A397588

精确目标：a(1)=1，n>1时a(n)=(n+1)Σ_{k=1}^{n−1}a(k)a(n−k)，∀n≥1，Odd(a(n)) ↔ ∃r≥0,n=2^r。文献裁决：完整镜像与本轮HTTP200原始JSON仍写Conjecture，但基线已有 `D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two`；主循环完整读 `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.lean`，源递推和正指标域与目标相符，`a_halving`及`a_odd_index_zero`给出活证明路径。冻结state的statement_id为 `sha256:01c1cad519e2e056064c9dbb822bbb04688d12c1ea8bc8584da0bc48c4eabee7`；published指公开仓内证明，未重编译。bind-only疑似声明即上述exact iff，high；仅换GF定义不构成新逃逸。数值方案可照抄：`N=256; a=[0]*(N+1); a[1]=1`，随后 `for n in range(2,N+1): a[n]=(n+1)*sum(a[k]*a[n-k] for k in range(1,n))`，用 `bool(a[n]%2)==(n&(n-1)==0)` 检查所有正指标；实际20项DATA全等、256个指标零反例、奇指标为1,2,4,8,16,32,64,128,256，计算0.014秒；勿照原递归程序重复指数展开。拟议逃逸：已被同题证明覆盖，无新目标。停止条件已触发为精确已证，drop。同族合派：零席，不另把中点卷积消去包装为独立靶。xref预检全部直接A号：无（comment/formula/xref均无直接A引用）；b-file未打开，ASSUMED-UNVERIFIED。

### A397265

精确靶是所有n≥1的恰一次多人并列计数r₂(n,1)=A007808(n)−n!，示例的“size at least 1”不替代定义中的2。目标和A007808、A397883均全文读完。已打开 https://arxiv.org/html/2607.02085v1 ：§2 Theorem3从首名块大小分类证明递推；§3 Theorem7及证明给g=(e^x−T_(m−1))^k/(2−T_(m−1))^(k+1)；§5 Example11 Eq(13)明确推导r₂(n,1)=Σ_(i=2)^n n!(n+1−i)/i!。A007808 %F的Freedman 2014公式是n!加此和（j=i−1），%C也写at most one tie，故原目标it appears已被公开证明及重索引覆盖，out/published/drop，bind风险high。仓内编号搜索未获同靶声明；普通有限求和和组合数引理无新逃逸。复制执行python3 numeric.py A397265：阶乘表、r_n=n r_(n−1)+Σ_(i=2)^n C(n,i)(n−i)!，另用A007808的b_n=(n²b_(n−1)−1)/(n−1)交叉核对，O(N²)整数运算，不枚举排列；1..200零差异，r5=311、r6=2383。无非bind逃逸可建议；同论文一般r_m(n,k)已覆盖A397883工具家族，0席，不把一般k换作新题。停止条件已经触发：打开了精确公式的推导。所有其余未打开源引文在JSON标ASSUMED-UNVERIFIED。数值初始化 r₀=0、b₁=1；上式 r_n 的第二项等于 n!·Σ_{i=2}^n1/i!，所以可用阶乘整除逐项累加，b₂起用给定递推；首n个b减n!作交叉检验。

### A396093

目标与六个直接引用均已逐字段全文读取；A166482 的 L-四连块论文证明的是铺砌解释，不自动证明本目标奇偶。已打开公开仓库固定 HEAD 的 RationalCompositionParityPeriodTen.lean 并与本地完整源码连读，证明位置为 `reduced_recurrence`、`parity_period_ten`、`odd_iff_mod_ten`、`even_at_even_index`、`even_at_odd_index_iff`：模二八阶递推只留偶间隔项，两次相差 2 的递推相加得到周期 10，初值奇余数恰 {1,3,7,9}。并非仅把 conjecture 改名：`generating_function_identity` 逐系数建立递推数列乘 D=N，`generating_function` 用非零常数项除法，`coefficients_unique` 强归纳对齐任意整系数解；末尾 `triple_B_eq_formula_two` 是 RatFunc ℚ 的三重复合恒等式，采用非零分母及 field_simp。故本地定义到 OEIS 公式(2)有实质桥，不只是含未证奇偶前提的条件结论。本次未编译、未检查 kernel 工件；结论是已读公开源码中有该证明，非本席认证构建。钉版 mathlib 实际读了 `Function.Periodic.map_mod_nat`（前提 hf 已是 Periodic）和 `PowerSeries.eq_mul_inv_iff_mul_eq`（前提分母常数非零），这些单独不产生周期或生成函数桥；D5 已补齐，故再做目标 high bind-only。数值 yes：整数递推 n≤500 与模二递推 n≤100000 全吻合，坏指标列表为空；O(8N) 算术、模二可 O(8) 空间滚动。拟议逃逸若是“模二递推推出周期十”，已被具名定理占用，现靶无可派新逃逸；不同迭代次数/不同模数需要另有精确未证命题及独立文献检索，不能顺手换题。停止：现靶直接 drop；若桥仅被误读，则回到 note-only，而不凭前缀宣称解决。两条奇偶子句是同一周期分类的投影，只算 1 个数学家族、当前 0 新席；A396094/209/210 只共用迭代有理函数工具，非同一命题。全部直接引用 A030267,A119821,A166482,A396094,A396209,A396210。  可复制运行：`python3 parity093.py`，完整脚本及 JSON 在本目录。核心算法： ```python r=[14,-75,196,-269,196,-75,14,-1] a=[0,1,6,33,174,892,4480,22149] for n in range(8,501): a.append(sum(r[k]*a[n-1-k] for k in range(8))) # 检验更长前缀时每步 %2，避免无用大整数。 ``` 检查的断言是 `a[n]%2 == (n%10 in (1,3,7,9))`。可照抄：`r=[14,-75,196,-269,196,-75,14,-1]; a=[0,1,6,33,174,892,4480,22149]`，随后 `for n in range(8,100001): a.append(sum(r[k]*a[n-1-k] for k in range(8))%2)`；初值检查亦取模，逐n断言 `a[n]%2==int(n%10 in (1,3,7,9))`。

### A397347

精确目标：a₁=1，Σ_{n≥1}a_n x^n/n=log(1+x+Σ_{n≥2}2n a_n x^n/(2n²−1))，∀n≥1，a_n≡[1,3,3,3]_(n−1 mod4)。文献裁决：本条仍标Conjecture，但xref指向A397346；主循环完整阅读基线 `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.lean` 后发现读者漏查的更强公开证明。该模块 `source_iff` 对齐A397346的源指数方程，`normalized_mod_eight` 给归一化b(2,n)≡6（n≡3 mod4），其余n≥2为2；源关系在有理数中为 a_n=(2n²−1)b(2,n)/2，因此模8先除2再乘奇因子，直接给本目标模4。bind-only疑似声明正是 `normalized_mod_eight`、`coeff_M_rat` 与 `source_iff`，high；主循环将原读者1档建议改为out/published/drop，published限公开仓内证明及上述规范化推论、未重编译。A397346 %F(6)漏了参数2，n=2会给14/3而非4；本裁决使用目标定义、%e正确关系及源码归一化，不依赖那行错式。数值方案可照抄：g=2，a=[0,1]、b=[0,1]；n=2..N令 s=Σ_{k=1}^{n−1}a_k b_{n−k}，追加 a_n=(g n²−1)s、b_n=g n s。只验余数则从每步起取mod4，O(N²)整数运算、O(N)存储，勿反复展开exp/log；主循环N=512、0.0074秒零反例，另精确算至29并与17项DATA全等。拟议卷积消去虽可重证，但现靶已被更强归一化定理覆盖，无新增逃逸。停止条件已触发；同族本目标零席，A397349的mod3残余须另核，不把它随模2族一并淘汰。xref预检全部直接A号（读者完整读）：A396846、A397346、A397349。四个条目的b-file均未打开，ASSUMED-UNVERIFIED；源码为本地已提交原文阅读，不冒称新开网页。

### A397902

精确域为零常数项的整数形式幂级数 A（若从 ℚ 上三角递推构造，整性仍须独立证明），目标是全部 n>2 的奇支撑分类，而非有限表或渐近式。已完整打开 manifest 中 A397902 及 A397591、A397596 的镜像文件：A397902 %C 是 Jul 20 2026 猜想，%F 的 Kotesovec 渐近没有奇偶证明；A397591 %C 是指数 m 的不同猜想，A397596 是指数 m、右端非零的不同定义，不能因为 Cf. 就移植结论。尝试 Google 精确 A 号+proof 仅得 JS 重定向、DuckDuckGo 得验证码、Yahoo 返回 500、Bing 返回与目标无关的酒店/CRM 结果（均有 web.json 收据）；这些不是有效的“无证明”检索，故文献状态 unknown，不冒升 tier 1。D5 的精确 A 号搜索未命中；已读 mathlib PowerSeries.coeff_pow 的完整类型与证明（Basic.lean:635，按 finsuppAntidiag 展开乘积），它只给系数展开，不给归一化除 m² 后的模二信息，故 bind 风险 med。可预登记的非绑定逃逸是：对逐级取 e=(n+1)² 的整系数三角递推，建立足够 2-adic 精度下可约去 e 的二进制进位消去引理，再推出模二支撑；单纯 Frobenius 模二会丢失偶 e 的除法信息，不能当见证。numeric=yes：numeric.py 的 exact integer power-coefficient recurrence，O(N³) 算术操作、O(N) 工作数组，N=80，首16项逐值与 %S/%T/%U 一致，n=3..80 零反例，奇指标为 1,3,4,5,6,7,8,13,14,15,16,29,30,31,32,61,62,63,64；不构成无界证明。停止条件：发现同域证明/反例即 drop；桥接只剩引用或除法整性/模二提升不能闭合则保持 note-only。族合并：A397902 与 A397594/A397592 只共享幂系数/2-adic 工具，平方指数不等价，不应冒算同一数学席；本项当前0实施席，确认文献并取得上述新提升引理后至多1探针席。全部直接引用：A397591、A397596。主循环另实测GitHub公开代码精确号加language:Lean查询，total_count=0、incomplete_results=false；只限索引，不替代无编号文献检索。其余未打开的源b-file及网页均ASSUMED-UNVERIFIED。可照抄的逐级公式：已知a₁…a_(n−1)，令e=(n+1)²、f=[1,−a₁,…,−a_(n−1),0]；c₀=1，j=1..n用 c_j=Σ_{i=1}^j(((e+1)i−j)f_i c_(j−i))/j 精确整除，然后 a_n=Σ_{j=0}^n c_j e^(n−j)/e；每次断言整除，N=80。

### A397594

本项固定 y=4，索引从0起，量词是全部 n>3；不能误用 A397591 从1起的偏移，也不能把 m² 指数的 A397902 当同一递推。目标及7个直接引用的全部字段已读：A397594 %C 为 Jul 10 2026 猜想，%F 给 a_y(n)=Σ y^k T(n,k)，A397590 %F(5)–(8)明列 y=0、1、2、3、4、5 与主对角 A180747；A375457 的右端是 m，其对数导数整除观察不是本题奇支撑证明。已打开 arXiv 精确 A397592 OR A397594 查询（family592-arxiv.web.json），totalResults=0；Brave 429，通用搜索仍不可作有效否定证据，所以只记搜索范围内未见证明、总裁定 unknown。D5 精确号及 Abel/diagonal parity 文字初筛未命中，mathlib 已读 PowerSeries.coeff_pow（Basic.lean:635）只展开幂；系数整数三角 T 若被完整证明，则偶 y 的取值模2都等于 T(n,0)，这两个目标只是 A397591 奇支撑的绑定推论，故 bind=high。源文件把 T 当整数三角展示却没有证明全部系数整性，不能把有限表提升成已确认的桥。拟议逃逸须放在族公共核心：证明 T∈ℤ[y][[x]] 的整性及 T(n,0) 在模2的二进制下降，或在有理递推中保持足够2-adic精度后证明可约去 m；这才超出参数代入，给单项再包一层不算新见证。numeric=yes：精确三角幂递推 N=100，O(N³)大整数算术、O(N)工作空间，A397594 前10项与源一致，n=4..100 零反例，奇指标0,1,2,5,7,9,15,17,31,33,63,65；与 y=0 的奇偶逐项相同。有限检查不能证明三角整性或全称支撑。停止条件：找到 A397591/三角核心同域证明后这些特例 drop；整性桥仍未核实或候选仅取 y=2/4 时保持 note-only。族合并为 A397592+A397594（连同非目标 A397591）最多1公共核心探针席，确认桥之前只称共享构造，确认桥之后两目标逻辑等价于同一常数列奇偶结论；不占两个实施席。全部直接引用为 A180747, A375457, A397590, A397591, A397592, A397593, A397595。主循环另实测GitHub公开代码精确号加language:Lean查询，total_count=0、incomplete_results=false；只限索引，不替代无编号文献检索。其余未打开的源b-file及网页均ASSUMED-UNVERIFIED。精确数值指令：a₀=1；n=1..100令m=n+1、P=Σ_{i<n}a_i x^i，先按A397902段的幂系数递推以e=m、f=[a₀,…,a_(n−1),0]算c_j=[x^j]P^m，再置a_n=((ym)^n−Σ_{j=0}^n c_j m^(n−j))/m，每次断言整除；y取本条参数，避免先mod2再除m。前轮A397591已列1/unknown/note-only，本轮不另给这个排除号计行或派席。

### A397592

本项固定 y=2，索引从0起，量词是全部 n>3；不能误用 A397591 从1起的偏移，也不能把 m² 指数的 A397902 当同一递推。目标及7个直接引用的全部字段已读：A397592 %C 为 Jul 10 2026 猜想，%F 给 a_y(n)=Σ y^k T(n,k)，A397590 %F(5)–(8)明列 y=0、1、2、3、4、5 与主对角 A180747；A375457 的右端是 m，其对数导数整除观察不是本题奇支撑证明。已打开 arXiv 精确 A397592 OR A397594 查询（family592-arxiv.web.json），totalResults=0；Brave 429，通用搜索仍不可作有效否定证据，所以只记搜索范围内未见证明、总裁定 unknown。D5 精确号及 Abel/diagonal parity 文字初筛未命中，mathlib 已读 PowerSeries.coeff_pow（Basic.lean:635）只展开幂；系数整数三角 T 若被完整证明，则偶 y 的取值模2都等于 T(n,0)，这两个目标只是 A397591 奇支撑的绑定推论，故 bind=high。源文件把 T 当整数三角展示却没有证明全部系数整性，不能把有限表提升成已确认的桥。拟议逃逸须放在族公共核心：证明 T∈ℤ[y][[x]] 的整性及 T(n,0) 在模2的二进制下降，或在有理递推中保持足够2-adic精度后证明可约去 m；这才超出参数代入，给单项再包一层不算新见证。numeric=yes：精确三角幂递推 N=100，O(N³)大整数算术、O(N)工作空间，A397592 前10项与源一致，n=4..100 零反例，奇指标0,1,2,5,7,9,15,17,31,33,63,65；与 y=0 的奇偶逐项相同。有限检查不能证明三角整性或全称支撑。停止条件：找到 A397591/三角核心同域证明后这些特例 drop；整性桥仍未核实或候选仅取 y=2/4 时保持 note-only。族合并为 A397592+A397594（连同非目标 A397591）最多1公共核心探针席，确认桥之前只称共享构造，确认桥之后两目标逻辑等价于同一常数列奇偶结论；不占两个实施席。全部直接引用为 A180747, A375457, A397590, A397591, A397593, A397594, A397595。主循环另实测GitHub公开代码精确号加language:Lean查询，total_count=0、incomplete_results=false；只限索引，不替代无编号文献检索。其余未打开的源b-file及网页均ASSUMED-UNVERIFIED。精确数值指令：a₀=1；n=1..100令m=n+1、P=Σ_{i<n}a_i x^i，先按A397902段的幂系数递推以e=m、f=[a₀,…,a_(n−1),0]算c_j=[x^j]P^m，再置a_n=((ym)^n−Σ_{j=0}^n c_j m^(n−j))/m，每次断言整除；y取本条参数，避免先mod2再除m。前轮A397591已列1/unknown/note-only，本轮不另给这个排除号计行或派席。

### A396491

完整读了本条及 A396351/A396353/A396354；本条 %C 明说插值所得 “should be treated as conjectural unless independently verified”。邻条 A396354 在 Jul 22 2026 提供四子句的证明思路，不能把 m=4 的结论绑定为 m=5。联网打开固定镜像 A396354 的 %C/%F，可见支持集界和 “The conjectured formula is true”；其 Aharoni–Linial DOI 只返回 Redirecting，论文未打开。Google 返回 JS 门、DuckDuckGo 返回验证码、Bing RSS 对 A396491 与 SAT 查询返回翻译/通信产品，故这些尝试不构成有效的阴性文献检索；全保存在 network.json，不能声称已搜尽。仓内逐字搜索无该计数声明；已读 `D5.S0.Certificates.LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable` 的类型与 rfl 证明，只把单个 Sat.Fmla 的空子句语义重述为不可满足，`Refutation.sound` 也不计多重集，不能直接给本条多项式；钉版 mathlib 的 Tarsi/minimal-unsatisfiable 字词搜索未见匹配声明。拟议非 bind-only 逃逸是对最多五子句的极小不可满足核按支持集与重叠作完整分类，并推得指定 k 集上的十个计数 b(k)；支持集上界 alone 不是逃逸的完整交付。数值 yes：sat_counts.py 用子句种类外层、子句数递增的 DP 保存满足赋值集的 AND 掩码，n=1..4 得 20,6760,244322,2703376，与公式相符；最大层状态数 41746，未枚举 n=5..10。该算法保留真值相同但文字多重集不同的子句类型，避免把模型错误商掉。每 n 的上界 O(m·binom(2n+2,3)·2^(2^n)) 个状态转移，稀疏字典在本次边界足够快。停止条件：找到同模型同量词证明即 drop；核分类遗漏重复子句/恒真子句则 invalid；只有插值或支持界则 note-only。与 A395546 同为 m=5，条件确认其导数桥后只占一个研究席；与 m=4 仅共享工具、不等价。当前未满足有效检索门，不推荐 dispatch。全部直接引用 A396351,A396353,A396354。  可复制运行：`python3 sat_counts.py`（脚本完整保存于本目录；M=5，n≤4，输出 sat_counts.json）。计数核心： ```python dp=[defaultdict(int) for _ in range(M+1)]; dp[0][full]=1 for mask in clause_masks:  # 每一种三文字多重集都出现一次     for j in range(1,M+1):         for old,v in list(dp[j-1].items()): dp[j][old & mask]+=v answer=dp[M][0] ```拟议系数为 B=(20,6720,224102,1766568,6055360,13099520,17940160,15088640,7096320,1433600)，靶为Σ_{k=1}^{10}B[k−1]·C(n,k)。可照抄掩码计数见文末共用SAT算法；一次M=5的运行同时读dp[4][0]、dp[5][0]，不枚举全部公式的笛卡尔幂。

### A396354

本条完整源同时保留旧的 “Conjecture” 与 Jul 22 2026 Alper Ferudun 的 “The conjectured formula is true”；不能只抓旧标签。已打开固定官方镜像 URL 的 %C 两段与 %F 后补段，证明路线为取 c 子句的极小不可满足核，删重文字后 Tarsi 给核支持≤c−1，余下 4−c 子句至多增 3(4−c) 个变量，故总支持≤7，再按指定有标号 k 集计数 b(k) 作 a(n)=Σb(k)C(n,k)，给出 b=(10,811,7178,16400,22000,15360,4480)。这确实是公开证明主张，而不是又一个猜想；但 DOI 10.1016/0097-3165(86)90060-9 的打开结果只有 Redirecting，且本次只独立检查 n≤4，没有确认 n=5..7 的计数证明材料，故依委托的“claimed proof cannot be confirmed”规则标 unknown/note-only，绝不标成可派的 tier 1。已读 A396351 与 A396353 的所有字段，Cook 1971 的复杂性背景不能提供固定 m 的多重集枚举定理。D5 的 `LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable` 与 `Refutation.sound` 只认证一个 CNF 的不可满足，未计支持、未计同真值不同子句；mathlib 字词搜索未见 Tarsi 计数声明。数值 yes：同 sat_counts.py 的 AND-mask 多重集 DP，在 n=1,2,3,4 得 10,831,9641,50018，与多项式一致；M=5 的共用运行最大状态数 41746，没有用 n≤4 证明 ∀n。计算复杂度界同上，严格保留重复文字与重复子句。可设想的逃逸是有限支持集上的完整核分类与 b(k) 的组合推导，但这正是既有公开证明所声称的内容；在核验文献前不得以重证包装求席。停止：确认该公开证明即 out/published/drop；发现系数反例即转 refutation；仅无法访问就维持 unknown。A396493 也是本 m=4 家族，至多一席且当前零实施席；与 A396491/A395546 的 m=5 仅共享分类工具，计数目标不同。全部直接 A 引用 A396351,A396353。  可复制运行：`python3 sat_counts.py`，读取 `counts["4"]` 与 `formula4`；n≤4 是独立真值掩码计数，不是直接重算插值多项式。若只需快速求公开公式值： ```python from math import comb B=(10,811,7178,16400,22000,15360,4480) def proposed(n): return sum(b*comb(n,k) for k,b in enumerate(B,1) if k<=n) ``` 此 O(7) 求值器以公式正确为前提，不作为其核验。档位out仅表示出现具体证明主张后暂退出开放靶池，文献unknown保留系数审计缺口，不把未核完写成published。可照抄掩码计数见文末共用SAT算法。

### A395896

精确目标：∀n∈ℕ，n 偶数 ⇒ |{k∈ℕ:1≤k<m², rad(k)|m, rad(k+1)|m}|=0，其中 m=A019565(n)。A019565 以 n 的第 j 个二进制位选择第 j 个素数；最低位为0当且仅当2不整除 m，所以“偶索引”准确对应“奇 m”。n=0 给 m=1，集合为空，边界无例外。已打开 https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem 的 “Lehmer’s algorithm” 段，原文明确写出 “Assume p1 = 2; otherwise there could be no consecutive P-smooth numbers, because all P-smooth numbers would be odd.” 这已经给出所需一般断言及证明理由，取 P 为 m 的素因子集即覆盖目标，无须 Pell 方程或 Størmer 的深层有限性。https://en.wikipedia.org/wiki/Radical_of_an_integer 的定义段确认 rad 为不同素因子乘积；因此 rad(k)|m 与 k 为 P-smooth 在正整数域等价。不是仅因条目写了 conjecture 而判新题。bind 风险 high：实读 pin 中 Nat.mem_primeFactors、Nat.Prime.mem_primeFactors、Nat.primeFactors_mono，以及 Nat.prod_primeFactors_dvd_iff（k≠0 时，素因子乘积整除 k iff 素因子集包含）。它们的证明是列表/有限集转换与整除传递，虽未直接命名本 A 序号，但加上相邻整数必有一个偶数就只剩索引和空集合包装；没有可推荐的非 bind-only escape。停止条件：一旦完成正整数、严格上界及索引换算即停止，不为凑席扩写 Lean。三条只占同一概念家族，计数为0与最大值哨兵−1等价；当前已知初等证明，合计0个新实施席；三个条目仍各占一个采集预算项。把偶 m 的完整分类或所有 primorial 上与无界 A002071/A002072 的相等式当 escape 会改变问题，且必须另证每个解 k<m²；Størmer 有限性不能给这个平方界。已打开 Eppstein 2007 “Smooth pairs” 的主文及评论，它报告有限素数集的计算与算法条件，没有证明此统一平方界；该桥仍 ASSUMED-UNVERIFIED。若升级到一般 S-unit/有效 abc 界的深核心，列 tier3 note-only、不计采集预算，不派发。全部直接 A 引用：A002071, A005117, A007947, A019565, A395754。

数值 yes：`python3 smooth_checks.py`；已运行全部 306 个平方自由 m≤500，以及 A019565 的索引 0≤n≤63（最大 m=30030），无奇 m 反例、无偶 m 缺少解、与三个源文件可比较的全部已列项一致。每个 m 完整生成 S={s≤m²:素因子均整除 m}，用集合查询 s+1；不是跳过奇 m 的循环论证。工作量 O(√m+ω(m)|S|)，存储 O(|S|)，单次生成每个素数阶段均只扩展原集合，不扫描 m² 个整数。可复制算法：
```python
def pairs(m):
    q,t,ps=2,m,[]
    while q*q<=t:
        if t%q==0:
            ps.append(q)
            while t%q==0:t//=q
        q+=1
    if t>1:ps.append(t)
    S={1}
    for p in ps:
        for s in list(S):
            v=s*p
            while v<=m*m:S.add(v);v*=p
    return sorted(k for k in S if k<m*m and k+1 in S)
print([(m,len(k:=pairs(m)),max(k,default=-1)) for m in [1,2,3,6,30]])
```
具体完整取样域及全部观察值保存于 smooth_checks.json；有限检查不替代无界定理。数值方案：先试除得到P=primeFactors(m)，S={1}；对每个p∈P及每个s∈list(S)，逐次乘p并仅加入≤m²的值，再取sorted(k for k in S if k<m² and k+1 in S)。完整代码见文末共用光滑数算法。读者实际检验306个平方自由m≤500与64个二进索引n≤63（最大m=30030），未见反例，与源可比DATA均相等；按生成集合大小工作，勿扫描至m²。其余未打开的源引文及页面全部ASSUMED-UNVERIFIED。

### A395754

精确目标：∀n≥1，令 m=A005117(n)，m 为奇数 ⇒ a(n)=0；a(n)=|K_m|，K_m={k∈ℕ:1≤k<m²,rad(k)|m,rad(k+1)|m}。平方自由索引从1开始，m=1 包含在空集情形；平方自由假设对奇偶排除实际多余。偶 m≥2 时 k=1 已给出 K_m 非空，所以零值分类恰为 m 奇数。已打开 https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem 的 “Lehmer’s algorithm” 段，原文明确写出 “Assume p1 = 2; otherwise there could be no consecutive P-smooth numbers, because all P-smooth numbers would be odd.” 这已经给出所需一般断言及证明理由，取 P 为 m 的素因子集即覆盖目标，无须 Pell 方程或 Størmer 的深层有限性。https://en.wikipedia.org/wiki/Radical_of_an_integer 的定义段确认 rad 为不同素因子乘积；因此 rad(k)|m 与 k 为 P-smooth 在正整数域等价。不是仅因条目写了 conjecture 而判新题。bind 风险 high：实读 pin 中 Nat.mem_primeFactors、Nat.Prime.mem_primeFactors、Nat.primeFactors_mono，以及 Nat.prod_primeFactors_dvd_iff（k≠0 时，素因子乘积整除 k iff 素因子集包含）。它们的证明是列表/有限集转换与整除传递，虽未直接命名本 A 序号，但加上相邻整数必有一个偶数就只剩索引和空集合包装；没有可推荐的非 bind-only escape。停止条件：一旦完成正整数、严格上界及索引换算即停止，不为凑席扩写 Lean。三条只占同一概念家族，计数为0与最大值哨兵−1等价；当前已知初等证明，合计0个新实施席；三个条目仍各占一个采集预算项。把偶 m 的完整分类或所有 primorial 上与无界 A002071/A002072 的相等式当 escape 会改变问题，且必须另证每个解 k<m²；Størmer 有限性不能给这个平方界。已打开 Eppstein 2007 “Smooth pairs” 的主文及评论，它报告有限素数集的计算与算法条件，没有证明此统一平方界；该桥仍 ASSUMED-UNVERIFIED。若升级到一般 S-unit/有效 abc 界的深核心，列 tier3 note-only、不计采集预算，不派发。全部直接 A 引用：A002071, A005117, A007947, A039956, A062503, A071403, A365435, A383008, A395721。

数值 yes：`python3 smooth_checks.py`；已运行全部 306 个平方自由 m≤500，以及 A019565 的索引 0≤n≤63（最大 m=30030），无奇 m 反例、无偶 m 缺少解、与三个源文件可比较的全部已列项一致。每个 m 完整生成 S={s≤m²:素因子均整除 m}，用集合查询 s+1；不是跳过奇 m 的循环论证。工作量 O(√m+ω(m)|S|)，存储 O(|S|)，单次生成每个素数阶段均只扩展原集合，不扫描 m² 个整数。可复制算法：
```python
def pairs(m):
    q,t,ps=2,m,[]
    while q*q<=t:
        if t%q==0:
            ps.append(q)
            while t%q==0:t//=q
        q+=1
    if t>1:ps.append(t)
    S={1}
    for p in ps:
        for s in list(S):
            v=s*p
            while v<=m*m:S.add(v);v*=p
    return sorted(k for k in S if k<m*m and k+1 in S)
print([(m,len(k:=pairs(m)),max(k,default=-1)) for m in [1,2,3,6,30]])
```
具体完整取样域及全部观察值保存于 smooth_checks.json；有限检查不替代无界定理。数值方案：先试除得到P=primeFactors(m)，S={1}；对每个p∈P及每个s∈list(S)，逐次乘p并仅加入≤m²的值，再取sorted(k for k in S if k<m² and k+1 in S)。完整代码见文末共用光滑数算法。读者实际检验306个平方自由m≤500与64个二进索引n≤63（最大m=30030），未见反例，与源可比DATA均相等；按生成集合大小工作，勿扫描至m²。其余未打开的源引文及页面全部ASSUMED-UNVERIFIED。

### A395721

精确目标：∀n≥1，令 m=A005117(n)，a(n)=max K_m（K_m为空时取−1）；猜想 m 奇数 ⇒ a(n)=−1。哨兵−1是整数值而非自然数截断减法；正整数集合有严格界 k<m²，故最大值存在。由偶 m≥2 的 k=1 见证，还可得 a(n)=−1 iff m 奇数；这仍是同一空集分类。已打开 https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem 的 “Lehmer’s algorithm” 段，原文明确写出 “Assume p1 = 2; otherwise there could be no consecutive P-smooth numbers, because all P-smooth numbers would be odd.” 这已经给出所需一般断言及证明理由，取 P 为 m 的素因子集即覆盖目标，无须 Pell 方程或 Størmer 的深层有限性。https://en.wikipedia.org/wiki/Radical_of_an_integer 的定义段确认 rad 为不同素因子乘积；因此 rad(k)|m 与 k 为 P-smooth 在正整数域等价。不是仅因条目写了 conjecture 而判新题。bind 风险 high：实读 pin 中 Nat.mem_primeFactors、Nat.Prime.mem_primeFactors、Nat.primeFactors_mono，以及 Nat.prod_primeFactors_dvd_iff（k≠0 时，素因子乘积整除 k iff 素因子集包含）。它们的证明是列表/有限集转换与整除传递，虽未直接命名本 A 序号，但加上相邻整数必有一个偶数就只剩索引和空集合包装；没有可推荐的非 bind-only escape。停止条件：一旦完成正整数、严格上界及索引换算即停止，不为凑席扩写 Lean。三条只占同一概念家族，计数为0与最大值哨兵−1等价；当前已知初等证明，合计0个新实施席；三个条目仍各占一个采集预算项。把偶 m 的完整分类或所有 primorial 上与无界 A002071/A002072 的相等式当 escape 会改变问题，且必须另证每个解 k<m²；Størmer 有限性不能给这个平方界。已打开 Eppstein 2007 “Smooth pairs” 的主文及评论，它报告有限素数集的计算与算法条件，没有证明此统一平方界；该桥仍 ASSUMED-UNVERIFIED。若升级到一般 S-unit/有效 abc 界的深核心，列 tier3 note-only、不计采集预算，不派发。全部直接 A 引用：A002072, A005117, A007947, A039956, A062503, A071403, A365435, A383008, A395754。

数值 yes：`python3 smooth_checks.py`；已运行全部 306 个平方自由 m≤500，以及 A019565 的索引 0≤n≤63（最大 m=30030），无奇 m 反例、无偶 m 缺少解、与三个源文件可比较的全部已列项一致。每个 m 完整生成 S={s≤m²:素因子均整除 m}，用集合查询 s+1；不是跳过奇 m 的循环论证。工作量 O(√m+ω(m)|S|)，存储 O(|S|)，单次生成每个素数阶段均只扩展原集合，不扫描 m² 个整数。可复制算法：
```python
def pairs(m):
    q,t,ps=2,m,[]
    while q*q<=t:
        if t%q==0:
            ps.append(q)
            while t%q==0:t//=q
        q+=1
    if t>1:ps.append(t)
    S={1}
    for p in ps:
        for s in list(S):
            v=s*p
            while v<=m*m:S.add(v);v*=p
    return sorted(k for k in S if k<m*m and k+1 in S)
print([(m,len(k:=pairs(m)),max(k,default=-1)) for m in [1,2,3,6,30]])
```
具体完整取样域及全部观察值保存于 smooth_checks.json；有限检查不替代无界定理。数值方案：先试除得到P=primeFactors(m)，S={1}；对每个p∈P及每个s∈list(S)，逐次乘p并仅加入≤m²的值，再取sorted(k for k in S if k<m² and k+1 in S)。完整代码见文末共用光滑数算法。读者实际检验306个平方自由m≤500与64个二进索引n≤63（最大m=30030），未见反例，与源可比DATA均相等；按生成集合大小工作，勿扫描至m²。其余未打开的源引文及页面全部ASSUMED-UNVERIFIED。
