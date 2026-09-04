# Governance

## Human Gates

Only four changes require explicit human approval:

1. Any change to `D5/X_Assumptions/`.
2. Any new axiom or change to the axiom-debt registry.
3. Signing or publishing a paper.
4. Any creation or modification of `Hearts.lean`.

Required-check configuration is also performed by a human operator; the repository records the permanent task but cannot claim that a hosting-platform setting is active.

## Meta-Layer Self-Modification

Changes to StrataLint, controlled vocabularies, agent charters, or the single repository specification require human approval and a dated Chronicle record. Chronicle history belongs to Git. The classifier does not classify its own authority: semantic classification and mathematical truth remain above the automated Gödel boundary.

## GROWTH-AUDIT: 性能候选队列

本节只登记增长与承载力候选,不定义 admission,不代表候选已获益。规范性性能账合同见 `docs/develop/spec/golden-ledger-repo-spec.md` A21。

P1 数据成熟阈统一为:目标 cohort × workload × kind × stage 至少有 30 个成功可比样本,覆盖至少 30 天,连续 14 天 observation/误报率均低于 5%,且最近窗口未发生 runner、workload 或 schema epoch 漂移。阈值未满足时,以下项目保持文档级候选,不得实施或声称收益。

| 候选 | 启动条件(P1 数据成熟后另须满足) | 待验证预测 | 收据边界 |
|---|---|---|---|
| 判官树缓存 | 〔勘注 2026-08-15:已落地——CI 判官/Scribe 发布目录按内容地址缓存(`.github/workflows/ci.yml` judge-cache,key 为 base 侧表达式对候选 tools 闭包的 hashFiles;admission 与 lean-inspect restore);原「不改变 base-owned judge 身份」前提随候选自判(2026-08-13)失效。before/after 收据未按 A21 P2 形式结案,状态记「实验」(实现已存在、收益未结案),由待启动候选转为未结案实验;落地路径为 CI 关键路径 PR,非经本表 P1 启动。〕 | — | — |
| lake cache 持久化 | 〔勘注 2026-08-15:已落地——`.lake` 经 actions/cache restore-keys 前缀回退跨 SHA 复用(`ci.yml` 中 path 含 `candidate/.lake` 的 restore 步及其 dev push save 步);同上,状态记「实验」(收益未按 P2 结案)。〕 | — | — |
| corpus 并行评估 | 〔勘注 2026-08-15:启动条件不可满足——`conservative` 阶段随保守扩展重放机器于 2026-08-12 整体退役,gate 已无该栏;候选关闭(不进入实验)。〕 | — | — |

候选一次只允许启动一个。结案必须引用 A21 的 P2 内容寻址 before/after 收据;无收据时状态只能是“候选”或“实验”,不得改写为“已优化”。
