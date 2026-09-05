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

internal static class JudgeSurfaceRevisionScanner
{
    private const string Head = "HEAD";

    private static readonly Regex GitInvocation = new(
        @"(?<![\w.\-/])git(?:\s+-C\s+\S+|\s+--?[\w\-]+(?:=\S+)?)*\s+"
        + @"(?<verb>show|cat-file|archive|worktree|checkout-index|checkout|restore|read-tree)\b"
        + @"(?<rest>[^|;&\n]*)",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static readonly Regex WorkflowRef = new(
        @"\bref:\s*(?<value>[^,}\n]+)",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static readonly Regex BaseRefIndicator = new(
        @"base_ref|pull_request\.base\b",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    internal static bool IsJudgeSurfacePath(string path) =>
        path.StartsWith(".github/", StringComparison.Ordinal)
        || path.StartsWith("tools/scripts/workflow/", StringComparison.Ordinal);

    internal static ImmutableArray<string> Scan(string path, string text)
    {
        var messages = ImmutableArray.CreateBuilder<string>();
        var isWorkflow = path.StartsWith(".github/workflows/", StringComparison.Ordinal)
            && (path.EndsWith(".yml", StringComparison.Ordinal)
                || path.EndsWith(".yaml", StringComparison.Ordinal));
        var lines = text.ReplaceLineEndings("\n").Split('\n');
        for (var index = 0; index < lines.Length; index++)
        {
            var line = lines[index];
            if (line.TrimStart().StartsWith('#'))
            {
                continue;
            }

            if (isWorkflow)
            {
                var reference = WorkflowRef.Match(line);
                if (reference.Success && BaseRefIndicator.IsMatch(reference.Groups["value"].Value))
                {
                    messages.Add(
                        $"line {index + 1}: actions/checkout ref '{reference.Groups["value"].Value.Trim()}' "
                        + "targets the protected base; the judge surface checks out only the checked object "
                        + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)");
                }
            }

            foreach (Match invocation in GitInvocation.Matches(line))
            {
                var verb = invocation.Groups["verb"].Value;
                var reason = Judge(verb, invocation.Groups["rest"].Value);
                if (reason is not null)
                {
                    messages.Add(
                        $"line {index + 1}: git {verb} {reason}; only HEAD may be materialized on the judge surface "
                        + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)");
                }
            }
        }

        return messages.ToImmutable();
    }

    private static string? Judge(string verb, string rest)
    {
        var tokens = rest.Replace("\"", string.Empty, StringComparison.Ordinal)
            .Replace("'", string.Empty, StringComparison.Ordinal)
            .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
        return verb switch
        {
            "worktree" => tokens.Length > 0 && tokens[0] == "add"
                ? "add materializes another revision's tree"
                : null,
            "read-tree" => "materializes a tree into the index",
            "checkout-index" => "materializes index contents",
            "restore" => RestoreSource(tokens),
            "checkout" => CheckoutRevision(tokens),
            "archive" => ArchiveRevision(tokens),
            "show" => RevisionPathOperand(tokens),
            "cat-file" => CatFileOperand(tokens),
            _ => null,
        };
    }

    private static string? RestoreSource(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--source" || token == "-s")
            {
                var source = index + 1 < tokens.Length ? tokens[index + 1] : string.Empty;
                return source == Head ? null : $"--source '{source}' materializes another revision's files";
            }

            if (token.StartsWith("--source=", StringComparison.Ordinal))
            {
                var source = token["--source=".Length..];
                return source == Head ? null : $"--source '{source}' materializes another revision's files";
            }
        }

        return null;
    }

    private static string? CheckoutRevision(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                return null;
            }

            if (token is "-b" or "-B" or "--orphan")
            {
                index++;
                continue;
            }

            if (token.StartsWith('-'))
            {
                continue;
            }

            return token == Head ? null : $"'{token}' materializes another revision";
        }

        return null;
    }

    private static string? ArchiveRevision(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                break;
            }

            if (token is "-o" or "--output" or "--remote" or "--exec" or "--format" or "--prefix")
            {
                index++;
                continue;
            }

            if (token.StartsWith('-'))
            {
                continue;
            }

            return token == Head ? null : $"'{token}' materializes another revision's tree";
        }

        return "without an explicit HEAD tree-ish is fail-closed";
    }

    private static string? RevisionPathOperand(string[] tokens)
    {
        foreach (var token in tokens)
        {
            if (token.StartsWith('-'))
            {
                continue;
            }

            var colon = token.IndexOf(':', StringComparison.Ordinal);
            if (colon <= 0)
            {
                continue;
            }

            var revision = token[..colon];
            if (revision != Head)
            {
                return $"'{token}' materializes a file of revision '{revision}'";
            }
        }

        return null;
    }

    private static string? CatFileOperand(string[] tokens)
    {
        if (tokens.Any(static token => token.StartsWith("--batch", StringComparison.Ordinal)))
        {
            return "--batch reads objects of unknown provenance (fail-closed)";
        }

        if (tokens.Contains("blob", StringComparer.Ordinal))
        {
            return "blob materializes an object of unknown provenance (fail-closed)";
        }

        return RevisionPathOperand(tokens);
    }
}
