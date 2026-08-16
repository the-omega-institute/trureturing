/- GID: D5/X_Frontier/SplitTool
   generality: G
   mirror-B: none(waiver:harness-ticket)
   mirror-E: none(waiver:harness-ticket)
   anchors: []
   digest: Implement deterministic local splitting when a capacity threshold is first reached. -/

/-- TASK D5-T0004
    Grow the C# `StrataLint split` subcommand only when a second real SL-003 capacity event arrives; the first (Engine/Rules 13 files) was resolved by moving the oversized rule into its own source file.
    曾试过并失败:2026-08-15:spec v7.11 R2 把 split 的形态由 Meta/ 下脚本改为 C# StrataLint 子命令,但编码旧形态的三处 harness 字面量未随迁,滞留至今;绊线所守路径在全仓历史中从未存在。 -/
def splitToolTicket : Unit := ()
