using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class CapacityAuditCommand
{
    private const string Usage = "USAGE: StrataLint capacity-audit";

    internal static ExplicitCommandResult Run(
        IReadOnlyList<string> arguments,
        string repositoryRoot)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        if (arguments.Count != 0)
        {
            return new ExplicitCommandResult(2, string.Empty, Usage + "\n");
        }

        try
        {
            var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
                .Select(static file => (file.RelativePath, File.ReadAllText(file.FullPath)))
                .ToArray();
            return Render(RepositoryCapacityAudit.InspectFiles(files));
        }
        catch (Exception exception)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE capacity-audit: {exception.Message}\n");
        }
    }

    internal static ExplicitCommandResult Render(
        IReadOnlyList<RepositoryCapacityFinding> findings)
    {
        ArgumentNullException.ThrowIfNull(findings);
        if (findings.Count == 0)
        {
            return new ExplicitCommandResult(0, string.Empty, string.Empty);
        }

        var output = string.Concat(findings
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
            .Select(static finding =>
                $"CAPACITY_AUDIT {finding.Path}: {finding.Message}\n"));
        return new ExplicitCommandResult(1, output, string.Empty);
    }
}
