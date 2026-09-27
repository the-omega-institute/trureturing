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
    private const int MaximumMetadataBytes = 64 * 1024 * 1024;
    private const int MaximumBatchBytes = 512 * 1024 * 1024;
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
            MaximumMetadataBytes);
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
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles) =>
        ReadFiles(indexedFiles,
            (arguments, maximumBytes, input) => BoundedProcessRunner.Run(
                "git", arguments, repositoryRoot, TimeSpan.FromSeconds(120), maximumBytes, input),
            MaximumBatchBytes);

    internal static IReadOnlyList<(string RelativePath, string Text)> ReadFiles(
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles,
        Func<IReadOnlyList<string>, int, ReadOnlyMemory<byte>, ProcessOutput> runGit,
        int maximumBatchBytes)
    {
        ArgumentNullException.ThrowIfNull(indexedFiles);
        ArgumentNullException.ThrowIfNull(runGit);
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(maximumBatchBytes);
        if (indexedFiles.Count == 0)
        {
            return [];
        }

        // Read the indexed object sizes, not working-tree files. Keep the existing
        // per-process bound while allowing the complete index to span many batches.
        var standardInput = Encoding.ASCII.GetBytes(string.Concat(
            indexedFiles.Select(static file => file.ObjectId + "\n")));
        var metadata = runGit(["cat-file", "--batch-check"], MaximumMetadataBytes, standardInput);
        if (metadata.ExitCode != 0)
        {
            throw new InvalidOperationException(ProcessError(metadata, "git cat-file --batch-check failed"));
        }

        var headers = StrictUtf8.GetString(metadata.StandardOutput).Split('\n');
        if (headers.Length != indexedFiles.Count + 1 || headers[^1].Length != 0)
        {
            throw new InvalidOperationException("git cat-file emitted an incomplete or extra size inventory");
        }

        var files = new List<(string RelativePath, string Text)>(indexedFiles.Count);
        var batch = new List<CapacityAuditIndexEntry>();
        var lengths = new List<int>();
        long batchBytes = 0;
        void ReadBatch()
        {
            var input = Encoding.ASCII.GetBytes(string.Concat(batch.Select(static file => file.ObjectId + "\n")));
            var result = runGit(["cat-file", "--batch"], maximumBatchBytes, input);
            if (result.ExitCode != 0)
            {
                throw new InvalidOperationException(ProcessError(result, "git cat-file --batch failed"));
            }

            files.AddRange(ParseBatch(batch, lengths, result.StandardOutput));
            batch.Clear();
            lengths.Clear();
            batchBytes = 0;
        }

        for (var index = 0; index < indexedFiles.Count; index++)
        {
            var file = indexedFiles[index];
            var length = ParseHeader(file, headers[index]);
            var outputBytes = (long)StrictUtf8.GetByteCount(headers[index]) + length + 2;
            if (outputBytes > maximumBatchBytes)
            {
                throw new InvalidOperationException($"indexed blob exceeds the supported batch size: {file.RelativePath}");
            }

            if (batch.Count != 0 && batchBytes + outputBytes > maximumBatchBytes)
            {
                ReadBatch();
            }

            batch.Add(file);
            lengths.Add(length);
            batchBytes += outputBytes;
        }

        ReadBatch();
        return files;
    }

    private static int ParseHeader(CapacityAuditIndexEntry indexedFile, string header)
    {
        var fields = header.Split(' ');
        if (fields.Length != 3
            || fields[0] != indexedFile.ObjectId
            || fields[1] != "blob"
            || !int.TryParse(fields[2], NumberStyles.None, CultureInfo.InvariantCulture, out var length)
            || length < 0)
        {
            throw new InvalidOperationException($"git cat-file emitted invalid metadata for {indexedFile.RelativePath}");
        }

        return length;
    }

    private static IReadOnlyList<(string RelativePath, string Text)> ParseBatch(
        IReadOnlyList<CapacityAuditIndexEntry> indexedFiles,
        IReadOnlyList<int> expectedLengths,
        byte[] output)
    {
        var files = new List<(string RelativePath, string Text)>(indexedFiles.Count);
        var offset = 0;
        for (var index = 0; index < indexedFiles.Count; index++)
        {
            var indexedFile = indexedFiles[index];
            var headerEnd = Array.IndexOf(output, (byte)'\n', offset);
            if (headerEnd < offset)
            {
                throw new InvalidOperationException(
                    $"git cat-file omitted metadata for {indexedFile.RelativePath}");
            }

            var header = StrictUtf8.GetString(output.AsSpan(offset, headerEnd - offset));
            var blobLength = ParseHeader(indexedFile, header);
            if (blobLength != expectedLengths[index])
            {
                throw new InvalidOperationException($"indexed blob size changed for {indexedFile.RelativePath}");
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
