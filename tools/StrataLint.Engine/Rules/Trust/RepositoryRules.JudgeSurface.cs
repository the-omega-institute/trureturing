using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    // SL-030 —— 判官面不得物化非 HEAD 修订的文件。
    //
    // CLAUDE.md 第 19 条「base 判官永久禁止」(τ=0 owner 2026-09-03 裁决)的机器投影:
    // 为判决候选而 checkout / restore / 编译 / 执行 base(或任何非受审 HEAD 修订)之代码
    // 的机制一律禁止;base 只以数据参与,而那条数据通道是候选判官自己的快照读者
    // (GitRepositorySnapshotReader),不是 shell。四次有案可查的 base 判官都长在这一层:
    //   `git worktree add --detach … "$ENGINEERING_BASE"`(2026-08-13 原型,483fb12e12^),
    //   `git show "HEAD^1:tools/scripts/workflow/engineering-base-floor.py" > … && python3 …`(#5210),
    //   `git show "HEAD^1:${ADMISSION_PLANE_CLASSIFIER_PATH}" > "$classifier"`(#5210 → #5285),
    //   `git show "HEAD^1:${PURE_REVERT_CLASSIFIER_PATH}" > "$classifier"`(3a2a11e34b → 7ffc6b054a)。
    // 故判据不是「执行了什么」(文本上不可判),而是「有没有把另一修订的文件物化进 shell」:
    // 能物化修订文件的 git 动词(show <rev>:<path>、cat-file、archive、worktree add、checkout <rev>、
    // restore --source、read-tree、checkout-index)在判官面上只许指向 HEAD;修订为变量时 fail-closed。
    // 作用面 = `.github/**`(workflow 与 CI 脚本)+ `tools/scripts/workflow/**`(CI 调用的 harness 脚本);
    // 这是四次案例全部发生的面。`tools/scripts/ingest.sh` 一类本地 producer 与 `tools/scripts/agent/**`
    // 不在面内:它们在 lane 里把 base 当数据读,不判决候选。
    private static bool JudgeSurfaceScoped(RepositoryFile artifact, RuleApplicabilityContext context) =>
        JudgeSurfaceRevisionScanner.IsJudgeSurfacePath(artifact.Path.Value);

    private static bool JudgeSurfaceAffected(RuleEvaluationContext context) =>
        Changed(context, JudgeSurfaceRevisionScanner.IsJudgeSurfacePath);

    private static ImmutableArray<RuleFinding> JudgeSurfaceRevisionMaterialization(
        RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in context.Current.Files
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            if (!JudgeSurfaceRevisionScanner.IsJudgeSurfacePath(path.Value)
                || file.IsOpaque
                || !context.IsBaseFactAffected(path.Value))
            {
                continue;
            }

            foreach (var message in JudgeSurfaceRevisionScanner.Scan(path.Value, file.Text))
            {
                findings.Add(new RuleFinding(path.Value, message));
            }
        }

        return findings.ToImmutable();
    }
}
