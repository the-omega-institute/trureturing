# 正交记录条件切片：预登记

产地：Codex implementation 席，lean4 skill；主循环实施，零独立评审席。
档位：第三档，issue #6298 的 observer→objective 形式化地形图。

question_answered：显式假设记录密度态两两乘积为零，能否证明其经典量子联合态
的实际偏迹互信息等于指针分布的 Shannon 熵？正交记录/环境分片结构是尚未采纳
的物理输入。本模块只证条件定理，不从 observer axiom 推出该结构，不加 axiom
或记录结构 instance，也不把任何熵恒等式放在假设位。

拟议 admission_basis: escape-witness。
拟议 escape_witness：正交支撑下的量子熵分解
S(Σ pᵢρᵢ)=H(p)+Σ pᵢS(ρᵢ)。
具名消费者：orthogonal_record_trace_gives_sbs_consensus。
量子熵分解若已有精确形式化，先另版登记并降级，再直接复用。

dominating_theorem_search：D5 与钉版 Mathlib 的 entropy/orthogonal/disjoint/block/mixture
检索未命中该量子等式。D5 的 MixtureEntropyUpperEquality 是经典概率版本；
Mathlib 的 JointEigenspace 给共同本征空间分解，没有矩阵熵接口。
CFC.posPart_negPart_unique 是可复用分析前置。第三方 GitHub 代码检索已实测可用，
正继续核对 physlib、Lean-QIT、csd-lean4；未宣称全生态搜索完备。
文献状态：该熵公式是已知量子信息结果，非新物理或新数学猜想。

拟议路线：用正交正算子的正负部分唯一性与函数演算证明负 x log x 的正交加性，
再证缩放项，有限和归纳得到熵分解；构造记录联合态并计算实际偏迹。
数值预登记：固定种子 6298，三组维度 (2,4)/(3,6)/(4,8)，各 80 个正交记录，
各 40 个一般随机记录；记录 max|I−H| 及非正交严格不等式计数，数值不作 kernel 证明。

utility: none。拟议声明皆为任意有限维一般定理，无有界枚举、检查器、数值归约
或固定参数认证实例。数值探针只存报告目录，不进入 D5。
落点：D5/S3/Quantum/Information（现有 3 文件）；Blueprint 同目录现有 3 个
非 md 文件；Quantum 已在 Meta/domains.yaml 注册，直接前置 generality G。

验收：serial-lean status=complete failed=0 → make lean-report（无 sorryAx/私 axiom）
→ make emit → make deposit-uncovered，再以精确 merge-base 跑 scribe-content-checks。
每个可编译单元即时 commit。允许只交正交熵分解并标清剩余联合态连接；
若无定理闭合则 blocked 并列失败路线，不以改写定义充数。
