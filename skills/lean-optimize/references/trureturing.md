# trureturing 适配

仅在目标仓库确为 trureturing 时使用。从当前检出的 `CLAUDE.md`、`AGENTS.md`、`agents/CONTEXT.md`、规范及相关技能读取现行规则；这里给出优化工作的路由，不替代它们。

## 工作树与任务范围

只读诊断复用当前检出，不新建工作树、不为状态回答启动 Lean。修改或会写构建产物的验证先按 CLAUDE.md §6.1 复用兼容 linked worktree，必要时用 `make worktree` 隔离；主检出保持 `dev`。

证明优化属于内容面工作，不能夹带修改 `tools/**`、验证器 Interface/Impl、`.github/**` 或其他判官面。实际问题在判官时，按现行规则披露具体阻塞并交所有者线，继续可做的内容优化。仅为性能调整读取但不绕过现有缓存锁；不使用 `LEAN_SKIP_LOCK=1` 排除等待以冒称提速。

Python 使用 3.12 或更新版本。长命令使用宿主作业/会话句柄，保持原生结束状态；其他工作树里的同名进程不属于本任务。

## 构建与验证

从 `make help` 核对当前入口；局部迭代必须有非空显式目标。例如，把下面点分名称替换为实际被测模块：

```sh
make lean LEAN_TARGETS="D5.Subject.Module"
make lean-report-scoped LEAN_TARGETS="D5.Subject.Module"
```

实际交付包含 Reg 源码时，把对应真实 `Reg.*` 目标加入列表；不要虚构镜像目标或只跑根包的裸 Lake 命令。常规迭代不需要整库 `make lean-report FULL_BUILD=1` 或 `make test FULL_BUILD=1`，最终所需检查仍按累计改动与 required checks 决定。

`make lean` 不带目标会走全项目及后续包；不要用它做单个证明的性能探针。缓存准备使用现有 `make lean-cache-ensure`，读取 `LEAN_CACHE` 中的 project/mathlib 状态、恢复方式和原因。warm 不保证 trace 当前，报告种子不相符也不自动证明正在全量重编。不要删除共享 `.lake`、伪造缓存状态或启动另一个 `warm-donor` 来代替诊断。

需要预热主检出 donor 时，先辨认已有作业。`make warm-donor FULL_BUILD=1` 会同步干净的主 `dev` 并触发完整 `make lean FULL_BUILD=1`，它是维护动作，不能当作免费的测量前置。缓存恢复与生产使用现有规范入口，不另造搬运器。

## 数学身份与冻结

复用既有声明时遵守先库后证；新增 helper 必须在活推导中有消费者。性能重写不是新数学成果的名义，也不免除新内容的准入规则。

记录优化前后的完整编译类型、定义变化与公理闭包。冻结成员、声明身份、Scribe、Reg 与消化状态由现役 writer 和相应检查处理；证明体变化也要检查冻结一致性。新的数学内容转入当前 `codex-formalize` 所拥有的流程，不因本技能而省掉准入、审查或冻结义务。

性能实验程序、必要数据和结果按 CLAUDE.md §2.10 归实验仓库；主仓库不新增 benchmark 日记、命令流水、重复快照或回执副本。规范与技能正文写当前通用规则，不复制某次构建的耗时、日期或事故叙述。

完成可恢复修改后按项目规则 checkpoint；提交、独立评审、PR、required checks 与交付范围仍由原任务和仓库规范决定。本技能不自动授权合并、发布缓存或改变远端配置。

仅在明确要求整库核验或具体集成义务无法由定向检查覆盖时调用全量入口，先说明原因，每条全量命令显式传入 `FULL_BUILD=1`；间接入口也适用。直接脚本调用使用该条命令的 `FULL_BUILD=1` 环境赋值。`make gate` / `ci-unit` 先读 `make gate-plan`，选中全量构建时同样显式确认。此为 agent 调用纪律，不宣称构建器已强制拒绝缺参；缓存失败、重试、最终检查和单纯文档修改均不构成全量理由。
