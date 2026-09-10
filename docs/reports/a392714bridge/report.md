# A392714 层 3 桥：实施报告

产地：Codex 主循环，lean4 skill；单点实施与自查，零独立评审席。
档位：用户指定的第二档研究线，第 3 层。原猜想尚未闭合。

## 预登记 v1（用户输入，保留原结算）

拟议见证是 Φ(n) 到 InResidual 的保号双射，不重证冻结的 signed_residual_sum。
该字面双射不成立：层 1 给出的 n=2 合格词是 (1,0,−1)、(0,1,−1)、
(1,−1,0)，剩余类只有最后一项。前两项由固定位置交换抵消。
因此应将“全体到剩余类的双射”改为“抵消后未配对词到剩余类的双射”。
本结论只否定双射的对象选择，不反驳原猜想。

## 预登记 v2（在新增 Lean 之前）

总路线：Φ(n) ↔ 倒序尾词；固定位置反号抵消；未配对词 ↔ InResidual；
核对排列 sign；直接应用层 2 求和。不能把抵消冒充双射。
首个独立可交付子步：对任意 m 和两个 Fin m 排列 a,b，显式生成
w=(a₁,−b₁,…,aₘ,−bₘ,0)，证明 Good 0 w 且所有固定块不可交换
当且仅当 InResidual a b；证明该编码单射，使用层 2 计算以 sign(a)sign(b)
赋权的这些编码的总和。拟议 escape_witness 是逐块归纳的前缀与区间条件对应，
以及从编码恢复 a,b 的构造。不是把所需 iff 放进假设。
该子步若通过 kernel，则即时 commit 并走 lean→lean-report→emit→deposit-uncovered。
它不声称任意未配对词的全分类，也不预设 word sign 等于产品 sign。
后续若可推进再扩展；本次结束时逐项标 proved/blocked，不留 sorry 或额外桥接假设。
两轮同型失败先换表述；无新可核验证明则以现有子步局部结算。

## 检索收据

- 本仓 D5：检索 A392714、Wronskian、suffixBudget、InResidual、signed_residual。
  精确命中层 2 ResidualPermutationSign.signed_residual_sum；无层 1 桥命中。
- 钉版 Mathlib：检索 sign、sumCongr、extendDomain、sum_take_ofFn。
  命中 Equiv.Perm.sign_sumCongr、sign_extendDomain、List.sum_take_ofFn 等通用接口；
  它们不提供本题前缀/不可交换分类。使用所需接口，不重证精确命中。
- GitHub API code search：A392714 language:Lean；“Wronskian” “permutation” language:Lean；
  两查询 total_count=0。只对该检索范围称未命中。
- arXiv v1 HTML：Remark 4 明写 parity imbalance 为 conjecture；乘积加权 Claim 4.1 不等于无权和。
- arXiv API all:A392714：唯一命中 2605.11137v2；继续打开 v2，Remark 5 仍明写同一 conjecture。
  在已查范围中无该无权结论的证明，不声称文献检索穷尽。
- OEIS search text、/A392714/internal、/A392714、search JSON 四入口均 HTTP 403；
  当前 OEIS 原文未能现场读取，不将层 1 的旧收据冒充本次读数。
- 原始外部响应放在 runner attempt，web-receipts.json 记录首批 URL 与响应状态。

## 落点与工具边界

起点 immutable SHA：`243104866264b7b14bfee9131f880ecce2154be1`。
新增前直接文件计数（Blueprint .md 不计）：`{"D5/S1/Words/Compositions": 8, "Blueprint/D5/S1/Words/Compositions": 8, "Library/Words": 34}`，上限 48。
Words 在 Meta/domains.yaml 注册于 S1；候选为 G，仅引入 G 的层 2 与 Mathlib。
头部按冻结模块的七行形状，utility: none。理由：所有定义与定理量化任意长度、
任意排列；不是有界枚举、checker、数值归约或有限认证实例。
初检 .lake 不存在；make lean 自动 clonefile 播种后两层 warm，EXIT=0。
未用裸 lake、native_decide；不改冻结层 2，不摄入自写理论卷。
shapes.sh 与 proof-edges.sh 已先读；后者直接执行裸 lake env lean，前者仍查旧 accepted 事件。
这与本任务禁止裸 lake、当前 state 片契约不匹配；后续依赖证据优先使用 make lean-report 的语义结果。
