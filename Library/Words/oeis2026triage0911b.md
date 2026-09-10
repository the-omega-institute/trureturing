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

当前批次已完成4条：A397588、A397265、A396093、A397347。完整收尾统计将在其余批次完成后写入。

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

## 逐条证据

### A397588

精确目标：a(1)=1，n>1时a(n)=(n+1)Σ_{k=1}^{n−1}a(k)a(n−k)，∀n≥1，Odd(a(n)) ↔ ∃r≥0,n=2^r。文献裁决：完整镜像与本轮HTTP200原始JSON仍写Conjecture，但基线已有 `D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two`；主循环完整读 `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.lean`，源递推和正指标域与目标相符，`a_halving`及`a_odd_index_zero`给出活证明路径。冻结state的statement_id为 `sha256:01c1cad519e2e056064c9dbb822bbb04688d12c1ea8bc8584da0bc48c4eabee7`；published指公开仓内证明，未重编译。bind-only疑似声明即上述exact iff，high；仅换GF定义不构成新逃逸。数值方案可照抄：`N=256; a=[0]*(N+1); a[1]=1`，随后 `for n in range(2,N+1): a[n]=(n+1)*sum(a[k]*a[n-k] for k in range(1,n))`，用 `bool(a[n]%2)==(n&(n-1)==0)` 检查所有正指标；实际20项DATA全等、256个指标零反例、奇指标为1,2,4,8,16,32,64,128,256，计算0.014秒；勿照原递归程序重复指数展开。拟议逃逸：已被同题证明覆盖，无新目标。停止条件已触发为精确已证，drop。同族合派：零席，不另把中点卷积消去包装为独立靶。xref预检全部直接A号：无（comment/formula/xref均无直接A引用）；b-file未打开，ASSUMED-UNVERIFIED。

### A397265

精确靶是所有n≥1的恰一次多人并列计数r₂(n,1)=A007808(n)−n!，示例的“size at least 1”不替代定义中的2。目标和A007808、A397883均全文读完。已打开 https://arxiv.org/html/2607.02085v1 ：§2 Theorem3从首名块大小分类证明递推；§3 Theorem7及证明给g=(e^x−T_(m−1))^k/(2−T_(m−1))^(k+1)；§5 Example11 Eq(13)明确推导r₂(n,1)=Σ_(i=2)^n n!(n+1−i)/i!。A007808 %F的Freedman 2014公式是n!加此和（j=i−1），%C也写at most one tie，故原目标it appears已被公开证明及重索引覆盖，out/published/drop，bind风险high。仓内编号搜索未获同靶声明；普通有限求和和组合数引理无新逃逸。复制执行python3 numeric.py A397265：阶乘表、r_n=n r_(n−1)+Σ_(i=2)^n C(n,i)(n−i)!，另用A007808的b_n=(n²b_(n−1)−1)/(n−1)交叉核对，O(N²)整数运算，不枚举排列；1..200零差异，r5=311、r6=2383。无非bind逃逸可建议；同论文一般r_m(n,k)已覆盖A397883工具家族，0席，不把一般k换作新题。停止条件已经触发：打开了精确公式的推导。所有其余未打开源引文在JSON标ASSUMED-UNVERIFIED。数值初始化 r₀=0、b₁=1；上式 r_n 的第二项等于 n!·Σ_{i=2}^n1/i!，所以可用阶乘整除逐项累加，b₂起用给定递推；首n个b减n!作交叉检验。

### A396093

目标与六个直接引用均已逐字段全文读取；A166482 的 L-四连块论文证明的是铺砌解释，不自动证明本目标奇偶。已打开公开仓库固定 HEAD 的 RationalCompositionParityPeriodTen.lean 并与本地完整源码连读，证明位置为 `reduced_recurrence`、`parity_period_ten`、`odd_iff_mod_ten`、`even_at_even_index`、`even_at_odd_index_iff`：模二八阶递推只留偶间隔项，两次相差 2 的递推相加得到周期 10，初值奇余数恰 {1,3,7,9}。并非仅把 conjecture 改名：`generating_function_identity` 逐系数建立递推数列乘 D=N，`generating_function` 用非零常数项除法，`coefficients_unique` 强归纳对齐任意整系数解；末尾 `triple_B_eq_formula_two` 是 RatFunc ℚ 的三重复合恒等式，采用非零分母及 field_simp。故本地定义到 OEIS 公式(2)有实质桥，不只是含未证奇偶前提的条件结论。本次未编译、未检查 kernel 工件；结论是已读公开源码中有该证明，非本席认证构建。钉版 mathlib 实际读了 `Function.Periodic.map_mod_nat`（前提 hf 已是 Periodic）和 `PowerSeries.eq_mul_inv_iff_mul_eq`（前提分母常数非零），这些单独不产生周期或生成函数桥；D5 已补齐，故再做目标 high bind-only。数值 yes：整数递推 n≤500 与模二递推 n≤100000 全吻合，坏指标列表为空；O(8N) 算术、模二可 O(8) 空间滚动。拟议逃逸若是“模二递推推出周期十”，已被具名定理占用，现靶无可派新逃逸；不同迭代次数/不同模数需要另有精确未证命题及独立文献检索，不能顺手换题。停止：现靶直接 drop；若桥仅被误读，则回到 note-only，而不凭前缀宣称解决。两条奇偶子句是同一周期分类的投影，只算 1 个数学家族、当前 0 新席；A396094/209/210 只共用迭代有理函数工具，非同一命题。全部直接引用 A030267,A119821,A166482,A396094,A396209,A396210。  可复制运行：`python3 parity093.py`，完整脚本及 JSON 在本目录。核心算法： ```python r=[14,-75,196,-269,196,-75,14,-1] a=[0,1,6,33,174,892,4480,22149] for n in range(8,501): a.append(sum(r[k]*a[n-1-k] for k in range(8))) # 检验更长前缀时每步 %2，避免无用大整数。 ``` 检查的断言是 `a[n]%2 == (n%10 in (1,3,7,9))`。可照抄：`r=[14,-75,196,-269,196,-75,14,-1]; a=[0,1,6,33,174,892,4480,22149]`，随后 `for n in range(8,100001): a.append(sum(r[k]*a[n-1-k] for k in range(8))%2)`；初值检查亦取模，逐n断言 `a[n]%2==int(n%10 in (1,3,7,9))`。

### A397347

精确目标：a₁=1，Σ_{n≥1}a_n x^n/n=log(1+x+Σ_{n≥2}2n a_n x^n/(2n²−1))，∀n≥1，a_n≡[1,3,3,3]_(n−1 mod4)。文献裁决：本条仍标Conjecture，但xref指向A397346；主循环完整阅读基线 `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.lean` 后发现读者漏查的更强公开证明。该模块 `source_iff` 对齐A397346的源指数方程，`normalized_mod_eight` 给归一化b(2,n)≡6（n≡3 mod4），其余n≥2为2；源关系在有理数中为 a_n=(2n²−1)b(2,n)/2，因此模8先除2再乘奇因子，直接给本目标模4。bind-only疑似声明正是 `normalized_mod_eight`、`coeff_M_rat` 与 `source_iff`，high；主循环将原读者1档建议改为out/published/drop，published限公开仓内证明及上述规范化推论、未重编译。A397346 %F(6)漏了参数2，n=2会给14/3而非4；本裁决使用目标定义、%e正确关系及源码归一化，不依赖那行错式。数值方案可照抄：g=2，a=[0,1]、b=[0,1]；n=2..N令 s=Σ_{k=1}^{n−1}a_k b_{n−k}，追加 a_n=(g n²−1)s、b_n=g n s。只验余数则从每步起取mod4，O(N²)整数运算、O(N)存储，勿反复展开exp/log；主循环N=512、0.0074秒零反例，另精确算至29并与17项DATA全等。拟议卷积消去虽可重证，但现靶已被更强归一化定理覆盖，无新增逃逸。停止条件已触发；同族本目标零席，A397349的mod3残余须另核，不把它随模2族一并淘汰。xref预检全部直接A号（读者完整读）：A396846、A397346、A397349。四个条目的b-file均未打开，ASSUMED-UNVERIFIED；源码为本地已提交原文阅读，不冒称新开网页。
