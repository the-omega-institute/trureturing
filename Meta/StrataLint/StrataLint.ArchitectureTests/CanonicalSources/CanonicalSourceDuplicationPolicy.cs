using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record CanonicalSourceDuplicationFinding(string Path, string Message);

internal static class CanonicalSourceDuplicationPolicy
{
    internal static IReadOnlyList<CanonicalSourceDuplicationFinding> InspectRepository(string repositoryRoot)
    {
        var backfillPath = Path.Combine(repositoryRoot, "Meta", "BACKFILL.yaml");
        var tickets = BackfillInventoryLoader.Load(File.ReadAllText(backfillPath))
            .RequireTickets()
            .Select(static ticket => (ticket.CaseId, ticket.Gid))
            .ToArray();
        var findings = new List<CanonicalSourceDuplicationFinding>();
        foreach (var path in Directory.EnumerateFiles(repositoryRoot, "*.cs", SearchOption.AllDirectories))
        {
            var relativePath = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
            if (relativePath.Split('/').Any(static segment => segment is ".git" or ".lake" or "bin" or "obj"))
            {
                continue;
            }

            findings.AddRange(InspectSource(relativePath, File.ReadAllText(path), tickets));
        }

        return findings;
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
}
