using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface ICapacityAuditFileAccess
{
    IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(string repositoryRoot);

    string ReadAllText(string fullPath);
}

internal sealed class ProductionCapacityAuditFileAccess : ICapacityAuditFileAccess
{
    internal static ProductionCapacityAuditFileAccess Instance { get; } = new();

    private ProductionCapacityAuditFileAccess()
    {
    }

    public IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(string repositoryRoot) =>
        GitIndexRepositoryFiles.Enumerate(repositoryRoot);

    public string ReadAllText(string fullPath) => File.ReadAllText(fullPath);
}

internal static class CapacityAuditCommand
{
    private const string Usage = "USAGE: StrataLint capacity-audit";

    internal static ExplicitCommandResult Run(
        IReadOnlyList<string> arguments,
        string repositoryRoot) =>
        Run(arguments, repositoryRoot, ProductionCapacityAuditFileAccess.Instance);

    internal static ExplicitCommandResult Run(
        IReadOnlyList<string> arguments,
        string repositoryRoot,
        ICapacityAuditFileAccess fileAccess)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(fileAccess);
        if (arguments.Count != 0)
        {
            return new ExplicitCommandResult(2, string.Empty, Usage + "\n");
        }

        IReadOnlyList<(string RelativePath, string FullPath)> indexedFiles;
        try
        {
            indexedFiles = fileAccess.Enumerate(repositoryRoot);
        }
        catch (Exception exception)
        {
            return InfrastructureFailure("index-enumeration", exception);
        }

        try
        {
            var files = indexedFiles
                .Select(file => (file.RelativePath, fileAccess.ReadAllText(file.FullPath)))
                .ToArray();
            return Render(RepositoryCapacityAudit.InspectFiles(files));
        }
        catch (Exception exception)
        {
            return InfrastructureFailure("file-read", exception);
        }
    }

    private static ExplicitCommandResult InfrastructureFailure(
        string stage,
        Exception exception) =>
        new(
            2,
            string.Empty,
            $"INFRASTRUCTURE_FAILURE capacity-audit: stage={stage} {exception.Message}\n");

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
