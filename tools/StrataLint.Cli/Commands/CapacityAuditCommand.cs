using System.Globalization;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CapacityAuditIndexEntry(string RelativePath, string ObjectId);

internal interface ICapacityAuditFileAccess
{
    IReadOnlyList<CapacityAuditIndexEntry> Enumerate(string repositoryRoot);

    IReadOnlyList<(string RelativePath, string Text)> ReadFiles(
        string repositoryRoot,
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles);
}

internal sealed class ProductionCapacityAuditFileAccess : ICapacityAuditFileAccess
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ProductionCapacityAuditFileAccess Instance { get; } = new();

    private ProductionCapacityAuditFileAccess()
    {
    }

    public IReadOnlyList<CapacityAuditIndexEntry> Enumerate(string repositoryRoot)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            ["ls-files", "--stage", "-z"],
            repositoryRoot,
            TimeSpan.FromSeconds(120),
            64 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(ProcessError(result, "git ls-files --stage failed"));
        }

        var entries = new Dictionary<string, CapacityAuditIndexEntry>(StringComparer.Ordinal);
        foreach (var encodedEntry in SplitNul(result.StandardOutput))
        {
            var tab = Array.IndexOf(encodedEntry, (byte)'\t');
            if (tab <= 0)
            {
                throw new InvalidOperationException("git index emitted invalid metadata");
            }

            var metadata = StrictUtf8.GetString(encodedEntry.AsSpan(0, tab)).Split(' ');
            var relativePath = StrictUtf8.GetString(encodedEntry.AsSpan(tab + 1));
            if (metadata.Length != 3
                || metadata[2] != "0"
                || !entries.TryAdd(
                    relativePath,
                    new CapacityAuditIndexEntry(relativePath, metadata[1])))
            {
                throw new InvalidOperationException(
                    $"unmerged or duplicate repository entry: {relativePath}");
            }
        }

        return entries.Values
            .OrderBy(static entry => entry.RelativePath, StringComparer.Ordinal)
            .ToArray();
    }

    public IReadOnlyList<(string RelativePath, string Text)> ReadFiles(
        string repositoryRoot,
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles)
    {
        if (indexedFiles.Count == 0)
        {
            return [];
        }

        var standardInput = Encoding.ASCII.GetBytes(string.Concat(
            indexedFiles.Select(static file => file.ObjectId + "\n")));
        var result = BoundedProcessRunner.Run(
            "git",
            ["cat-file", "--batch"],
            repositoryRoot,
            TimeSpan.FromSeconds(120),
            512 * 1024 * 1024,
            standardInput);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(ProcessError(result, "git cat-file --batch failed"));
        }

        return ParseBatch(indexedFiles, result.StandardOutput);
    }

    private static IReadOnlyList<(string RelativePath, string Text)> ParseBatch(
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles,
        byte[] output)
    {
        var files = new List<(string RelativePath, string Text)>(indexedFiles.Count);
        var offset = 0;
        foreach (var indexedFile in indexedFiles)
        {
            var headerEnd = Array.IndexOf(output, (byte)'\n', offset);
            if (headerEnd < offset)
            {
                throw new InvalidOperationException(
                    $"git cat-file omitted metadata for {indexedFile.RelativePath}");
            }

            var header = StrictUtf8.GetString(output.AsSpan(offset, headerEnd - offset));
            var fields = header.Split(' ');
            if (fields.Length != 3
                || fields[0] != indexedFile.ObjectId
                || fields[1] != "blob"
                || !int.TryParse(
                    fields[2],
                    NumberStyles.None,
                    CultureInfo.InvariantCulture,
                    out var blobLength)
                || blobLength < 0)
            {
                throw new InvalidOperationException(
                    $"git cat-file emitted invalid metadata for {indexedFile.RelativePath}");
            }

            offset = headerEnd + 1;
            if (blobLength > output.Length - offset - 1
                || output[offset + blobLength] != (byte)'\n')
            {
                throw new InvalidOperationException(
                    $"git cat-file emitted truncated content for {indexedFile.RelativePath}");
            }

            files.Add((indexedFile.RelativePath, ReadText(output, offset, blobLength)));
            offset += blobLength + 1;
        }

        if (offset != output.Length)
        {
            throw new InvalidOperationException("git cat-file emitted unexpected trailing content");
        }

        return files;
    }

    private static string ReadText(byte[] bytes, int offset, int length)
    {
        using var stream = new MemoryStream(bytes, offset, length, writable: false);
        using var reader = new StreamReader(
            stream,
            Encoding.UTF8,
            detectEncodingFromByteOrderMarks: true);
        return reader.ReadToEnd();
    }

    private static string ProcessError(ProcessOutput result, string fallback) =>
        Encoding.UTF8.GetString(result.StandardError).Trim() is { Length: > 0 } error
            ? error
            : fallback;

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index <= bytes.Length; index++)
        {
            if (index != bytes.Length && bytes[index] != 0)
            {
                continue;
            }

            if (index > start)
            {
                yield return bytes[start..index];
            }
            start = index + 1;
        }
    }
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

        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles;
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
            var files = fileAccess.ReadFiles(repositoryRoot, indexedFiles);
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
