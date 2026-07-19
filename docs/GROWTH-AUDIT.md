# GROWTH-AUDIT

本文件只登记增长与承载力候选,不定义 admission,不代表候选已获益。规范性性能账合同见 `docs/develop/spec/golden-ledger-repo-spec.md` A21。

## 性能候选队列

P1 数据成熟阈统一为:目标 cohort × workload × kind × stage 至少有 30 个成功可比样本,覆盖至少 30 天,连续 14 天 observation/误报率均低于 5%,且最近窗口未发生 runner、workload 或 schema epoch 漂移。阈值未满足时,以下项目保持文档级候选,不得实施或声称收益。

| 候选 | 启动条件(P1 数据成熟后另须满足) | 待验证预测 | 收据边界 |
|---|---|---|---|
| 判官树缓存 | `setup`/`build-judge` 同栏 p95 合计至少占 gate p95 的 10%,且绝对值 ≥60s;能以精确 base commit、toolchain 与 judge tree 内容地址证明失效边界 | 缓存命中降低判官准备 p95 ≥20%,不改变 base-owned judge 身份 | before/after 同 cohort 与 cache_state 分栏;附缓存地址、命中判据、失效攻击案及完整 gate rc |
| lake cache 持久化 | `lean-reports` 同栏 p95 ≥120s,且 warm/cold 分栏显示持久化可解释的 ≥20% 差值;磁盘保留预算和淘汰策略已登记 | 跨 run 持久化降低 `lean-reports` p95 ≥20%,不复用输入地址不等的产物 | before/after 同 cohort、同 report input address;附磁盘峰值/余量、淘汰收据与错误命中反例 |
| corpus 并行评估 | `conservative` 同栏 p95 ≥120s 且占 gate p95 ≥20%;host_concurrency/loadavg_per_cpu 表明至少两个稳定执行槽;每案独立性与输出排序已由确定性测试证明 | 有界并行降低 conservative p95 ≥20%,逐案结果与 canonical certificate bytes 不变 | before/after 同 cohort、同 corpus 地址与并发档;附串并行 byte-equality、峰值 RSS/fd 与失败取消语义 |

候选一次只允许启动一个。结案必须引用 A21 的 P2 内容寻址 before/after 收据;无收据时状态只能是“候选”或“实验”,不得改写为“已优化”。
