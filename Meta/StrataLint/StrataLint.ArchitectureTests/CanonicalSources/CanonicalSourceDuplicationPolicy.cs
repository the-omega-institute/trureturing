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
    internal const int MinimumBlueprintPassageLength = 96;
    internal const int MinimumBlueprintWordCount = 14;

    internal const string AtomizerRegistryPath =
        "Meta/StrataLint/StrataLint.Engine/Digestion/AtomizerRegistry.cs";

    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectRepository(string repositoryRoot)
    {
        var backfillPath = Path.Combine(repositoryRoot, "Meta", "BACKFILL.yaml");
        var backfill = BackfillInventoryLoader.Load(File.ReadAllText(backfillPath));
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
                TimeSpan.FromSeconds(1))
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
                where Regex.IsMatch(
                    literal.Token.ValueText,
                    $"(?<![A-Za-z0-9.-]){Regex.Escape(id)}(?![A-Za-z0-9.-])",
                    RegexOptions.CultureInvariant,
                    TimeSpan.FromSeconds(1))
                select new CanonicalSourceDuplicationFinding(
                    path,
                    $"C# atomizer id literal {id} duplicates Meta/BACKFILL.yaml; dispatch through AtomizerRegistry"))
            .ToArray();
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
            if (!patterns.Any(pattern => Regex.IsMatch(
                    source,
                    pattern,
                    RegexOptions.CultureInvariant | RegexOptions.Singleline,
                    TimeSpan.FromSeconds(1))))
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
                    TimeSpan.FromSeconds(1)))
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
            TimeSpan.FromSeconds(1))
        .Select(static passage => passage.Trim())
        .Where(static passage => passage.Length > 0);

    private static bool IsAuthoredEnglishPassage(string passage) =>
        passage.Length >= MinimumBlueprintPassageLength
        && passage[^1] is '.' or '!' or '?'
        && Regex.Matches(
            passage,
            "[A-Za-z]+(?:['-][A-Za-z]+)*",
            RegexOptions.CultureInvariant,
            TimeSpan.FromSeconds(1)).Count >= MinimumBlueprintWordCount;

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
