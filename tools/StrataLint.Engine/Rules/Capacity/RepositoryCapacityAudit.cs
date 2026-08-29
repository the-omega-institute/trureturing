namespace StrataLint.Engine;

internal sealed record RepositoryCapacityFinding(string Path, string Message);

internal static class RepositoryCapacityAudit
{
    internal static IReadOnlyList<RepositoryCapacityFinding> InspectFiles(
        IEnumerable<(string Path, string Text)> files)
    {
        var findings = new List<RepositoryCapacityFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, text) in files)
        {
            if (RepositoryRules.IsCapacityExcluded(path))
            {
                continue;
            }

            var lineCount = RepositoryRules.CountArtifactLines(text);
            if (lineCount > RepositoryRules.ArtifactHardLineLimit)
            {
                findings.Add(new RepositoryCapacityFinding(
                    path,
                    $"artifact spans {lineCount} lines (hard limit "
                    + $"{RepositoryRules.ArtifactHardLineLimit})"));
            }

            var slash = path.LastIndexOf('/');
            var directory = slash < 0 ? "." : path[..slash];
            directories[directory] = directories.GetValueOrDefault(directory) + 1;
        }

        findings.AddRange(directories
            .Where(item => item.Value > RepositoryRules.DirectoryToleranceLimit)
            .OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => new RepositoryCapacityFinding(
                item.Key,
                $"directory contains {item.Value} files (admission limit "
                + $"{RepositoryRules.DirectoryFileLimit}, repository tolerance "
                + $"{RepositoryRules.DirectoryToleranceLimit}; split per CLAUDE.md 8)")));
        return findings;
    }
}
