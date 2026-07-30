using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record CanonicalSourceDuplicationFinding(string Path, string Message);

internal static class CanonicalSourceDuplicationPolicy
{
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
        var findings = new List<CanonicalSourceDuplicationFinding>();
        foreach (var (relativePath, path) in CSharpRepositorySources.Enumerate(repositoryRoot))
        {
            var source = File.ReadAllText(path);
            findings.AddRange(InspectSource(relativePath, source, tickets));
            findings.AddRange(InspectDomainMappings(relativePath, source, domains));
            findings.AddRange(InspectAtomizerIdLiterals(relativePath, source, atomizerIds));
            findings.AddRange(InspectSpecificationCopies(relativePath, source, specification));
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

        return SplitSpecificationPassages(specification)
            .Select(static passage => passage.Trim())
            .Where(static passage => passage.Length >= 64 && CountCjk(passage) >= 24)
            .Distinct(StringComparer.Ordinal)
            .Where(passage => source.Contains(passage, StringComparison.Ordinal))
            .Select(passage => new CanonicalSourceDuplicationFinding(
                path,
                $"fixture copies a {passage.Length}-character passage from the canonical specification; use neutral synthetic text"))
            .ToArray();
    }

    private static IEnumerable<string> SplitSpecificationPassages(string specification)
    {
        var start = 0;
        for (var index = 0; index < specification.Length; index++)
        {
            var current = specification[index];
            if (current is '。' or '！' or '？')
            {
                yield return specification[start..(index + 1)];
                start = index + 1;
                continue;
            }

            if (current is not ('\r' or '\n'))
            {
                continue;
            }

            var delimiterStart = index;
            var cursor = index;
            var lineBreaks = 0;
            while (cursor < specification.Length)
            {
                if (specification[cursor] == '\r'
                    && cursor + 1 < specification.Length
                    && specification[cursor + 1] == '\n')
                {
                    lineBreaks++;
                    cursor += 2;
                    continue;
                }

                if (specification[cursor] == '\n')
                {
                    lineBreaks++;
                    cursor++;
                    continue;
                }

                break;
            }

            if (lineBreaks < 2)
            {
                index = cursor - 1;
                continue;
            }

            yield return specification[start..delimiterStart];
            start = cursor;
            index = cursor - 1;
        }

        yield return specification[start..];
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

    private static int CountCjk(string value) => value.Count(static character =>
        character is >= '\u3400' and <= '\u4dbf'
            or >= '\u4e00' and <= '\u9fff');

    private static IEnumerable<(string RelativePath, string FullPath)> EnumerateToml(
        string repositoryRoot)
    {
        foreach (var path in Directory.EnumerateFiles(
                     repositoryRoot,
                     "*.toml",
                     SearchOption.AllDirectories))
        {
            var relativePath = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
            if (relativePath.Split('/').Any(static segment =>
                    segment is ".git" or ".lake" or "bin" or "obj"))
            {
                continue;
            }

            yield return (relativePath, path);
        }
    }
}
