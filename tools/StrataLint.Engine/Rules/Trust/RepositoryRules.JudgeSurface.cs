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

    // Global options between `git` and the verb: each option token (`-C`, `-c`, `--git-dir`,
    // `--work-tree`, `--namespace`, `--no-pager`, …) may carry one separated value token, so
    // `git --git-dir "$dir" cat-file -p "$oid"` still reaches the verb (review round 3 escape).
    // A first token that is not an option (`git commit -m "show x"`) is not a judge-surface verb.
    private static readonly Regex GitInvocation = new(
        @"(?<![\w.\-/])git(?:\s+-[^\s|;&]*(?:\s+[^\s|;&\-][^\s|;&]*)?)*\s+"
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

            // Deliberately scan after '#': quoted text can hide a command, so trailing comments stay fail-closed.
            if (isWorkflow)
            {
                // Deliberately over-match: this line scanner cannot see YAML structure; a visible Block beats a silent miss.
                var reference = WorkflowRef.Match(line);
                if (reference.Success && BaseRefIndicator.IsMatch(reference.Groups["value"].Value))
                {
                    messages.Add(
                        $"line {index + 1}: a `ref:` naming the protected base "
                        + $"'{reference.Groups["value"].Value.Trim()}' is not allowed on the judge surface "
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
        var tokens = Arguments(rest);
        return verb switch
        {
            "worktree" => WorktreeAddRevision(tokens),
            "read-tree" => ReadTreeOperands(tokens),
            "checkout-index" => "materializes index contents whose provenance is not a revision (fail-closed)",
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

    // The git arguments of one invocation: quotes stripped, cut at the first shell redirection
    // (`>`, `2>`, `<`) or comment (`#…`) token. Anything after those is a file name or prose, never
    // a git operand; classifying it as one produced both false positives (`> log` read as a
    // commit-ish) and false negatives (`# -e` read as a metadata mode) in review round 3.
    private static string[] Arguments(string rest)
    {
        var tokens = rest.Replace("\"", string.Empty, StringComparison.Ordinal)
            .Replace("'", string.Empty, StringComparison.Ordinal)
            .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
        var end = Array.FindIndex(tokens, static token => IsShellRedirection(token) || token.StartsWith('#'));
        return end < 0 ? tokens : tokens[..end];
    }

    // `git worktree add [options] <path> [<commit-ish>]`. Options are a closed table: an option
    // this table does not know fails closed, because an unknown option may consume the next token
    // and shift which positional is the commit-ish (review round 3: `--reason HEAD /tmp/h "$BASE"`).
    private static readonly HashSet<string> WorktreeAddFlags = new(StringComparer.Ordinal)
    {
        "--detach", "--lock", "-f", "--force", "--checkout", "--no-checkout", "--orphan",
        "-q", "--quiet", "--track", "--no-track", "--guess-remote", "--no-guess-remote",
        "--relative-paths", "--no-relative-paths", "--",
    };

    private static readonly HashSet<string> WorktreeAddOptionsWithArgument = new(StringComparer.Ordinal)
    {
        "-b", "-B", "--reason",
    };

    private static string? WorktreeAddRevision(string[] tokens)
    {
        if (tokens.Length == 0 || tokens[0] != "add")
        {
            return null;
        }

        var positional = new List<string>();
        for (var index = 1; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (WorktreeAddOptionsWithArgument.Contains(token))
            {
                index++;
                continue;
            }

            if (WorktreeAddFlags.Contains(token) || token.StartsWith("--reason=", StringComparison.Ordinal))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"add option '{token}' is not in the closed option table (fail-closed)";
            }

            positional.Add(token);
        }

        if (positional.Count < 2 || positional[1] == Head)
        {
            return null;
        }

        return $"add commit-ish '{positional[1]}' materializes another revision's tree";
    }

    private static readonly HashSet<string> ReadTreeFlags = new(StringComparer.Ordinal)
    {
        "-m", "-u", "-i", "-n", "-v", "--reset", "--empty", "--dry-run", "--trivial", "--aggressive",
        "--no-sparse-checkout", "--debug-unpack", "--",
    };

    private static string? ReadTreeOperands(string[] tokens)
    {
        var foundTree = false;
        foreach (var token in tokens)
        {
            if (ReadTreeFlags.Contains(token)
                || token.StartsWith("--prefix=", StringComparison.Ordinal)
                || token.StartsWith("--index-output=", StringComparison.Ordinal)
                || token.StartsWith("--exclude-per-directory=", StringComparison.Ordinal))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"option '{token}' is not in the closed option table (fail-closed)";
            }

            foundTree = true;
            if (token != Head && token != "HEAD^{tree}")
            {
                return $"tree-ish '{token}' materializes another revision into the index";
            }
        }

        return foundTree ? null : "without a tree-ish is fail-closed";
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

    // `git cat-file`: the FIRST mode token decides. Metadata modes (-e/-t/-s) never materialize;
    // --batch* reads objects of unknown provenance; content modes (-p, blob/tree/commit/tag,
    // --textconv, --filters) must name a literal HEAD object. Tokens after a redirection or `#`
    // never reach this method (see Arguments), so a `-e` in a comment cannot flip the mode.
    private static string? CatFileOperand(string[] tokens)
    {
        var modeIndex = Array.FindIndex(tokens, static token => IsCatFileMode(token));
        if (modeIndex < 0)
        {
            return RevisionPathOperand(tokens);
        }

        var mode = tokens[modeIndex];
        if (mode.StartsWith("--batch", StringComparison.Ordinal))
        {
            return "--batch reads objects of unknown provenance (fail-closed)";
        }

        if (mode is "-e" or "-t" or "-s")
        {
            return null;
        }

        var foundOperand = false;
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (index == modeIndex || token.StartsWith('-'))
            {
                continue;
            }

            foundOperand = true;
            if (!IsLiteralHeadObject(token))
            {
                return $"operand '{token}' materializes an object of another revision";
            }
        }

        return foundOperand ? null : $"content mode '{mode}' without an operand is fail-closed";
    }

    private static bool IsCatFileMode(string token) =>
        token is "-e" or "-t" or "-s" or "-p" or "blob" or "tree" or "commit" or "tag"
            or "--textconv" or "--filters"
        || token.StartsWith("--batch", StringComparison.Ordinal);

    // Exact allow-list: `HEAD^{/regex}` and `HEAD^{…}` in general can walk history
    // (`HEAD^{/derive}` resolved to an ancestor in review round 3), so only the two peel forms
    // that cannot leave the checked object are literal HEAD here.
    private static bool IsLiteralHeadObject(string operand) =>
        operand == Head
        || operand == "HEAD^{tree}"
        || operand == "HEAD^{commit}"
        || (operand.StartsWith("HEAD:", StringComparison.Ordinal) && operand.Length > "HEAD:".Length);

    private static bool IsShellRedirection(string token)
    {
        var index = 0;
        while (index < token.Length && char.IsAsciiDigit(token[index]))
        {
            index++;
        }

        return index < token.Length && token[index] is '<' or '>';
    }
}
