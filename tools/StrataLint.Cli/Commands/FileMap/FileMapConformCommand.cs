using System.Text;

namespace StrataLint.Cli;

internal static class FileMapConformCommand
{
    internal const string Usage = "USAGE: StrataLint filemap-conform";

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
            return Render(FileMapPolicy.InspectRepository(repositoryRoot));
        }
        catch (Exception exception)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE filemap-conform: {exception.Message}\n");
        }
    }

    internal static ExplicitCommandResult Render(IReadOnlyList<FileMapFinding> findings)
    {
        ArgumentNullException.ThrowIfNull(findings);
        if (findings.Count == 0)
        {
            return new ExplicitCommandResult(0, string.Empty, string.Empty);
        }

        var output = new StringBuilder();
        foreach (var finding in findings
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Code, StringComparer.Ordinal))
        {
            output.Append(finding.Code);
            output.Append(' ');
            output.Append(finding.Path);
            output.Append(": ");
            output.Append(finding.Message);
            output.Append('\n');
        }

        return new ExplicitCommandResult(1, output.ToString(), string.Empty);
    }
}
