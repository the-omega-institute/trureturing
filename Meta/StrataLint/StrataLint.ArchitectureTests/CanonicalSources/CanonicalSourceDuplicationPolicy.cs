using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record CanonicalSourceDuplicationFinding(string Path, string Message);
internal sealed record CanonicalBlueprintPassage(string Path, string Text);

internal static class CanonicalSourceDuplicationPolicy
{
    // 正则的超时按**壁钟**计,所以它同时在量两件事:模式是否跑飞,以及本机此刻有多忙。
    // 原值 1 秒把后者也放进了判词——2026-08-11 一夜三次 RegexMatchTimeoutException 假红,
    // 两次直接掐掉整轮 gate,而同样的输入隔离重跑全绿。
    //
    // 不删超时:本文件的模式若真跑飞,无超时就是挂死,在 20 分钟 job 预算下比假红更糟。
    // 改为把预算放到负载碰不到、又仍能兜住真跑飞的量级。这些模式都是线性形状
    // (转义字面量加简单前后瞻),正常耗时在微秒级,30 秒与 1 秒对「是否跑飞」的判别力相同,
    // 对「本机是否繁忙」的敏感度则相差三十倍。
    private static readonly TimeSpan RegexRunawayBudget = TimeSpan.FromSeconds(30);

    internal const int MinimumBlueprintPassageLength = 96;
    internal const int MinimumBlueprintWordCount = 14;

    internal const string AtomizerRegistryPath =
        "Meta/StrataLint/StrataLint.Engine/Digestion/AtomizerRegistry.cs";

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectRepository(string repositoryRoot)
    {
        var backfill = BackfillInventoryLoader.LoadRoot(repositoryRoot);
        var tickets = backfill.RequireTickets()
            .Select(static ticket => (ticket.CaseId, ticket.Gid))
            .ToArray();
        var atomizerIds = backfill.RequireDigestionSources()
            .Select(static source => source.Atomizer)
            .Where(static id => id != AtomizerRegistry.NoAtomizerId)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        var specification = File.ReadAllText(Path.Combine(
            repositoryRoot,
            BootstrapGate.SpecificationPath));
        var domains = LoadDomains(repositoryRoot);
        var csharpSources = CSharpRepositorySources.Enumerate(repositoryRoot)
            .Select(static file => (
                Path: file.RelativePath,
                Source: File.ReadAllText(file.FullPath)))
            .ToArray();
        var blueprintPassages = ExtractBlueprintPassages(csharpSources.Where(
            static file => IsBlueprintSource(file.Path)));
        var findings = new List<CanonicalSourceDuplicationFinding>();
        foreach (var (relativePath, source) in csharpSources)
        {
            findings.AddRange(InspectSource(relativePath, source, tickets));
            findings.AddRange(InspectDomainMappings(relativePath, source, domains));
            findings.AddRange(InspectAtomizerIdLiterals(relativePath, source, atomizerIds));
            findings.AddRange(InspectSpecificationCopies(relativePath, source, specification));
            findings.AddRange(InspectBlueprintCopies(
                relativePath,
                source,
                blueprintPassages));
        }

        foreach (var (relativePath, path) in EnumerateToml(repositoryRoot))
        {
            findings.AddRange(InspectSpecificationCopies(
                relativePath,
                File.ReadAllText(path),
                specification));
        }

        return findings;
    }

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectSpecificationCopies(
        string path,
        string source,
        string specification)
    {
        if (string.Equals(path, BootstrapGate.SpecificationPath, StringComparison.Ordinal))
        {
            return [];
        }

        return Regex.Split(
                specification,
                "(?<=[。！？])|(?:\\r?\\n){2,}",
                RegexOptions.CultureInvariant,
                RegexRunawayBudget)
            .Select(static passage => passage.Trim())
            .Where(static passage => passage.Length >= 64 && CountCjk(passage) >= 24)
            .Distinct(StringComparer.Ordinal)
            .Where(passage => source.Contains(passage, StringComparison.Ordinal))
            .Select(passage => new CanonicalSourceDuplicationFinding(
                path,
                $"fixture copies a {passage.Length}-character passage from the canonical specification; use neutral synthetic text"))
            .ToArray();
    }

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectBlueprintCopies(
        string path,
        string source,
        IEnumerable<(string Path, string Source)> blueprintSources) =>
        InspectBlueprintCopies(path, source, ExtractBlueprintPassages(blueprintSources));

    private static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectBlueprintCopies(
        string path,
        string source,
        IReadOnlyList<CanonicalBlueprintPassage> blueprintPassages)
    {
        if (IsBlueprintSource(path))
        {
            return [];
        }

        var literals = ExtractConstantStrings(source);
        return blueprintPassages
            .Where(passage => literals.Any(literal =>
                literal.Contains(passage.Text, StringComparison.Ordinal)))
            .Select(passage => new CanonicalSourceDuplicationFinding(
                path,
                $"C# literal copies a {passage.Text.Length}-character authored passage from {passage.Path}; reference the canonical Blueprint source instead"))
            .ToArray();
    }

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectAtomizerIdLiterals(
        string path,
        string source,
        IEnumerable<string> atomizerIds)
    {
        if (string.Equals(path, AtomizerRegistryPath, StringComparison.Ordinal))
        {
            return [];
        }

        var ids = atomizerIds.ToHashSet(StringComparer.Ordinal);
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return (from literal in root.DescendantNodes().OfType<LiteralExpressionSyntax>()
                where literal.IsKind(SyntaxKind.StringLiteralExpression)
                from id in ids
                where ContainsWholeToken(literal.Token.ValueText, id)
                select new CanonicalSourceDuplicationFinding(
                    path,
                    $"C# atomizer id literal {id} duplicates Meta/BACKFILL.yaml; dispatch through AtomizerRegistry"))
            .ToArray();
    }

    // 原先这里对每个 (字符串字面量 × atomizer id) 组合内插一个新模式调用静态
    // Regex.IsMatch。静态重载按模式串缓存,而默认缓存只有 15 条 —— 模式随 id 变化,
    // 于是几乎每次调用都重新编译一遍;这既是该测试单跑就要 48s 的原因,也是它那
    // 1 秒**壁钟**超时的暴露面:满载时微秒级的匹配也能超时,同一棵树时绿时红
    // (2026-08-11 一夜三次假红,两次直接掐掉整轮 gate)。
    //
    // 判定本身不需要正则:「该字面量是否整词包含此 id」= 一次序数扫描加边界字符检查。
    // 无模式缓存、无回溯、无壁钟依赖 —— 判词只由输入决定(器律④:修产生处,产好原材料)。
    private static bool ContainsWholeToken(string text, string token)
    {
        for (var index = text.IndexOf(token, StringComparison.Ordinal);
             index >= 0;
             index = text.IndexOf(token, index + 1, StringComparison.Ordinal))
        {
            if (!IsTokenCharacter(index - 1) && !IsTokenCharacter(index + token.Length))
            {
                return true;
            }
        }

        return false;

        bool IsTokenCharacter(int at) =>
            at >= 0
            && at < text.Length
            && (char.IsAsciiLetterOrDigit(text[at]) || text[at] is '.' or '-');
    }

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectSource(
        string path,
        string source,
        IEnumerable<(string CaseId, string Gid)> tickets)
    {
        var findings = new List<CanonicalSourceDuplicationFinding>();
        foreach (var ticket in tickets)
        {
            var caseId = Regex.Escape(ticket.CaseId);
            var gid = Regex.Escape(ticket.Gid);
            var patterns = new[]
            {
                $"\\[\\s*\"{gid}\"\\s*\\]\\s*=\\s*\"{caseId}\"",
                $"\\[\\s*\"{gid}\"\\s*\\]\\s*=\\s*\\[[^\\]]*\"{caseId}\"[^\\]]*\\]",
                $"\\[\\s*\"{gid}\"\\s*\\]\\s*=\\s*new\\s*(?:string\\s*)?\\[\\s*\\]\\s*\\{{[^}}]*\"{caseId}\"[^}}]*\\}}",
                $"\\[\\s*\"{caseId}\"\\s*\\]\\s*=\\s*\"{gid}\"",
                $"\\(\\s*\"{caseId}\"\\s*,\\s*\"{gid}\"\\s*\\)",
                $"\\(\\s*\"{gid}\"\\s*,\\s*\"{caseId}\"\\s*\\)",
            };
            // 同上:模式随 ticket 内插,静态缓存必然抖动。绝大多数源文件两个串一个都不含,
            // 故先用序数 Contains 预筛,把正则调用降到实际可能命中的极少数文件上。
            if (!source.Contains(ticket.CaseId, StringComparison.Ordinal)
                || !source.Contains(ticket.Gid, StringComparison.Ordinal))
            {
                continue;
            }

            if (!patterns.Any(pattern => Regex.IsMatch(
                    source,
                    pattern,
                    RegexOptions.CultureInvariant | RegexOptions.Singleline,
                    RegexRunawayBudget)))
            {
                continue;
            }

            findings.Add(new CanonicalSourceDuplicationFinding(
                path,
                $"C# literal mapping {ticket.CaseId} <-> {ticket.Gid} duplicates Meta/BACKFILL.yaml; use BackfillInventoryLoader"));
        }

        return findings;
    }

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectDomainMappings(
        string path,
        string source,
        IEnumerable<(string Name, string Stratum)> domains)
    {
        var registeredNames = domains
            .Select(static domain => domain.Name)
            .ToHashSet(StringComparer.Ordinal);
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var findings = new List<CanonicalSourceDuplicationFinding>();
        foreach (var assignment in root.DescendantNodes().OfType<AssignmentExpressionSyntax>())
        {
            if (!assignment.IsKind(SyntaxKind.SimpleAssignmentExpression)
                || assignment.Left is not ImplicitElementAccessSyntax indexer
                || indexer.ArgumentList.Arguments.Count != 1
                || indexer.ArgumentList.Arguments[0].Expression is not LiteralExpressionSyntax key
                || !key.IsKind(SyntaxKind.StringLiteralExpression)
                || assignment.Right is not LiteralExpressionSyntax value
                || !value.IsKind(SyntaxKind.StringLiteralExpression)
                || !registeredNames.Contains(key.Token.ValueText)
                || !Regex.IsMatch(
                    value.Token.ValueText,
                    "^S[0-4]$",
                    RegexOptions.CultureInvariant,
                    RegexRunawayBudget))
            {
                continue;
            }

            findings.Add(new CanonicalSourceDuplicationFinding(
                path,
                $"C# dictionary literal maps registered domain {key.Token.ValueText} to stratum {value.Token.ValueText}; use Meta/domains.yaml through RegistryLoader"));
        }

        return findings;
    }

    private static (string Name, string Stratum)[] LoadDomains(string repositoryRoot)
    {
        var outcome = RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(repositoryRoot, "Meta", "registry.yaml")),
            File.ReadAllBytes(Path.Combine(repositoryRoot, "Meta", "domains.yaml")));
        if (outcome is not RegistryLoadOutcome.Accepted accepted)
        {
            throw new InvalidOperationException("Canonical registry and domain vocabulary must load.");
        }

        return accepted.Policy.Domains
            .Select(static domain => (domain.Key.Value, domain.Value.ToString()))
            .ToArray();
    }

    private static IReadOnlyList<CanonicalBlueprintPassage> ExtractBlueprintPassages(
        IEnumerable<(string Path, string Source)> blueprintSources) => blueprintSources
        .SelectMany(source => ExtractConstantStrings(source.Source)
            .SelectMany(SplitSentences)
            .Where(IsAuthoredEnglishPassage)
            .Select(passage => new CanonicalBlueprintPassage(source.Path, passage)))
        .DistinctBy(static passage => passage.Text, StringComparer.Ordinal)
        .ToArray();

    private static IReadOnlyList<string> ExtractConstantStrings(string source)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return root.DescendantNodes()
            .OfType<ExpressionSyntax>()
            .Where(static expression => expression.Parent switch
            {
                ParenthesizedExpressionSyntax => false,
                BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.AddExpression) => false,
                _ => true,
            })
            .Select(TryEvaluateConstantString)
            .Where(static value => value is not null)
            .Select(static value => value!)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
    }

    private static string? TryEvaluateConstantString(ExpressionSyntax expression) => expression switch
    {
        LiteralExpressionSyntax literal when literal.IsKind(SyntaxKind.StringLiteralExpression) =>
            literal.Token.ValueText,
        ParenthesizedExpressionSyntax parenthesized =>
            TryEvaluateConstantString(parenthesized.Expression),
        BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.AddExpression) =>
            TryEvaluateConstantString(binary.Left) is { } left
            && TryEvaluateConstantString(binary.Right) is { } right
                ? left + right
                : null,
        _ => null,
    };

    private static IEnumerable<string> SplitSentences(string value) => Regex.Split(
            value,
            "(?<=[.!?])(?=\\s|$)",
            RegexOptions.CultureInvariant,
            RegexRunawayBudget)
        .Select(static passage => passage.Trim())
        .Where(static passage => passage.Length > 0);

    private static bool IsAuthoredEnglishPassage(string passage) =>
        passage.Length >= MinimumBlueprintPassageLength
        && passage[^1] is '.' or '!' or '?'
        && Regex.Matches(
            passage,
            "[A-Za-z]+(?:['-][A-Za-z]+)*",
            RegexOptions.CultureInvariant,
            RegexRunawayBudget).Count >= MinimumBlueprintWordCount;

    private static bool IsBlueprintSource(string path) =>
        path.StartsWith("Blueprint/", StringComparison.Ordinal)
        && path.EndsWith(".scribe.cs", StringComparison.Ordinal);

    private static int CountCjk(string value) => value.Count(static character =>
        character is >= '\u3400' and <= '\u4dbf'
            or >= '\u4e00' and <= '\u9fff');

    private static IEnumerable<(string RelativePath, string FullPath)> EnumerateToml(
        string repositoryRoot) => GitIndexRepositoryFiles.Enumerate(repositoryRoot)
        .Where(static file => file.RelativePath.EndsWith(".toml", StringComparison.Ordinal));
}
