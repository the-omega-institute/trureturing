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

当前批次已完成1条：A397588。完整收尾统计将在其余批次完成后写入。

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

## 逐条证据

### A397588

精确目标：a(1)=1，n>1时a(n)=(n+1)Σ_{k=1}^{n−1}a(k)a(n−k)，∀n≥1，Odd(a(n)) ↔ ∃r≥0,n=2^r。文献裁决：完整镜像与本轮HTTP200原始JSON仍写Conjecture，但基线已有 `D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two`；主循环完整读 `D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.lean`，源递推和正指标域与目标相符，`a_halving`及`a_odd_index_zero`给出活证明路径。冻结state的statement_id为 `sha256:01c1cad519e2e056064c9dbb822bbb04688d12c1ea8bc8584da0bc48c4eabee7`；published指公开仓内证明，未重编译。bind-only疑似声明即上述exact iff，high；仅换GF定义不构成新逃逸。数值方案可照抄：`N=256; a=[0]*(N+1); a[1]=1`，随后 `for n in range(2,N+1): a[n]=(n+1)*sum(a[k]*a[n-k] for k in range(1,n))`，用 `bool(a[n]%2)==(n&(n-1)==0)` 检查所有正指标；实际20项DATA全等、256个指标零反例、奇指标为1,2,4,8,16,32,64,128,256，计算0.014秒；勿照原递归程序重复指数展开。拟议逃逸：已被同题证明覆盖，无新目标。停止条件已触发为精确已证，drop。同族合派：零席，不另把中点卷积消去包装为独立靶。xref预检全部直接A号：无（comment/formula/xref均无直接A引用）；b-file未打开，ASSUMED-UNVERIFIED。
