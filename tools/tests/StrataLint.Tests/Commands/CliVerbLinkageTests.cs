using System.Collections.Immutable;
using System.Text.RegularExpressions;
using StrataLint.Cli;

namespace StrataLint.Tests;

// 引用完整性(CLAUDE.md 第Ⅵ节「引用必须机械可判,悬空即红」):凡一处工件指向一个 CLI 动词,
// 就必须有机器验证那个动词存在。
//
// 立条案由:`make c0-verify` / `make c0-reconcile-trust-root` / `make record-golden` 三个目标
// 各自把一个 dispatch 表里不存在的动词交给 CLI,实跑得 `UNKNOWN_COMMAND ... exit=2`。
// 既有的 MakeWorkflowTests 对此全绿——它断言的是「Makefile 文本里有这段字符串」,
// 验的是语法不是指向;而它自己又带 [Trait("Category","Script")],不在默认测试集内。
//
// 本测试刻意是纯 in-process 断言(不 spawn 进程),因此不带 Script 分类,
// 落在 `make -C tools test` 真正执行的那一批里。
public sealed class CliVerbLinkageTests
{
    // 提取器至少应认出这么多次调用。低于此,说明提取器自己坏了(路径变了、调用形态变了),
    // 而不是「仓库很干净」——零匹配的 glob 不得静默通过。
    private const int MinimumRecognisedInvocations = 10;

    private readonly record struct VerbInvocation(string File, int Line, string Verb);

    [Fact]
    public void EveryCliVerbTheRepositoryInvokesIsImplemented()
    {
        var root = TestRepositoryLayout.FindRoot();
        var invocations = CollectInvocations(root);

        Assert.True(
            invocations.Length >= MinimumRecognisedInvocations,
            $"the verb extractor recognised only {invocations.Length} invocation(s); "
                + "it is broken, not the repository");

        var implemented = CliApplication.ImplementedCommands.ToHashSet(StringComparer.Ordinal);
        var dangling = invocations
            .Where(invocation => !implemented.Contains(invocation.Verb))
            .OrderBy(invocation => invocation.Verb, StringComparer.Ordinal)
            .ThenBy(invocation => invocation.File, StringComparer.Ordinal)
            .ToArray();

        Assert.True(
            dangling.Length == 0,
            "these callers name a CLI verb the dispatch table does not implement:\n"
                + string.Join(
                    '\n',
                    dangling.Select(invocation =>
                        $"  {invocation.File}:{invocation.Line}  {invocation.Verb}")));
    }

    // `dotnet run --project <cli> --configuration Release -- <verb>` 与
    // `dotnet "$SOME_DLL" <verb>`:动词是 CLI 分隔符之后的第一个 token。
    private static readonly Regex AfterSeparator = new(
        @"(?<![\w-])--\s+(?<verb>[a-z][a-z0-9-]*)",
        RegexOptions.CultureInvariant);

    private static readonly Regex AfterAssembly = new(
        @"dotnet\s+""?\$\{?\w+\}?""?\s+(?<verb>[a-z][a-z0-9-]*)",
        RegexOptions.CultureInvariant);

    // playbook-workflows.sh 的 CLI 转发函数;它把参数原样交给 `dotnet run … -- "$@"`。
    private static readonly Regex ThroughForwarder = new(
        @"(?<![\w-])run_cli\s+(?<verb>[a-z][a-z0-9-]*)",
        RegexOptions.CultureInvariant);

    private static ImmutableArray<VerbInvocation> CollectInvocations(string root)
    {
        var builder = ImmutableArray.CreateBuilder<VerbInvocation>();
        foreach (var file in CallerFiles(root))
        {
            var relative = Path.GetRelativePath(root, file).Replace('\\', '/');
            foreach (var (line, text) in LogicalLines(File.ReadAllLines(file)))
            {
                if (text.TrimStart().StartsWith('#'))
                {
                    continue;
                }

                var namesTheCli = text.Contains("StrataLint.Cli.csproj", StringComparison.Ordinal)
                    || text.Contains("StrataLint.dll", StringComparison.Ordinal)
                    || text.Contains("$PROJECT", StringComparison.Ordinal)
                    || text.Contains("$CLI_PROJECT", StringComparison.Ordinal)
                    || text.Contains("$JUDGE_DLL", StringComparison.Ordinal);

                if (namesTheCli)
                {
                    // 一条命令里可能出现多个 `--` 分隔符:例如 ingest.sh 先用一个把被包装的命令
                    // 交给 report-consumer,CLI 自己的动词在最后一个分隔符之后。取最后一个。
                    var separated = AfterSeparator.Matches(text);
                    if (separated.Count > 0)
                    {
                        builder.Add(new VerbInvocation(
                            relative,
                            line,
                            separated[^1].Groups["verb"].Value));
                    }

                    foreach (Match match in AfterAssembly.Matches(text))
                    {
                        builder.Add(new VerbInvocation(relative, line, match.Groups["verb"].Value));
                    }
                }

                foreach (Match match in ThroughForwarder.Matches(text))
                {
                    builder.Add(new VerbInvocation(relative, line, match.Groups["verb"].Value));
                }
            }
        }

        return builder.ToImmutable();
    }

    private static IEnumerable<string> CallerFiles(string root)
    {
        var makefile = Path.Combine(root, "Makefile");
        if (File.Exists(makefile))
        {
            yield return makefile;
        }

        var toolsMakefile = Path.Combine(root, "tools", "Makefile");
        if (File.Exists(toolsMakefile))
        {
            yield return toolsMakefile;
        }

        foreach (var directory in new[]
                 {
                     Path.Combine(root, "tools", "scripts"),
                     Path.Combine(root, ".github", "scripts"),
                 })
        {
            if (!Directory.Exists(directory))
            {
                continue;
            }

            foreach (var script in Directory
                         .EnumerateFiles(directory, "*.sh", SearchOption.AllDirectories)
                         .OrderBy(static path => path, StringComparer.Ordinal))
            {
                yield return script;
            }
        }
    }

    // shell 与 make 的续行合并成一条逻辑行,行号保留续行块的首行,便于诊断定位。
    private static IEnumerable<(int Line, string Text)> LogicalLines(string[] lines)
    {
        for (var index = 0; index < lines.Length; index++)
        {
            var first = index;
            var text = lines[index];
            while (text.EndsWith('\\') && index + 1 < lines.Length)
            {
                text = string.Concat(text.AsSpan(0, text.Length - 1), " ", lines[++index].Trim());
            }

            yield return (first + 1, text);
        }
    }

}
