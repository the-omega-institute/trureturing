using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static class ScribeDeltaInputLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ScribeDeltaInputs Load(
        string repositoryRoot,
        string baseRevision,
        string changesFile,
        string producerPathsFile)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        if (baseRevision.Length is not (40 or 64) || !baseRevision.All(char.IsAsciiHexDigit))
        {
            throw new ArgumentException("Scribe delta base must be an exact git object ID.", nameof(baseRevision));
        }

        var changesPath = Path.GetFullPath(changesFile, repositoryRoot);
        var producerPath = Path.GetFullPath(producerPathsFile, repositoryRoot);
        var changes = RawChangeSet.Create(ReadNulPaths(changesPath));
        var producerPaths = ParseProducerPaths(ReadLines(producerPath));
        ValidateBase(repositoryRoot, baseRevision);
        ValidateChangeManifest(repositoryRoot, baseRevision, changes);
        ValidateProducerManifest(repositoryRoot, producerPaths);
        return ScribeDeltaInputs.Create(
            baseRevision,
            changes,
            producerPaths,
            path => ReadBaseDocument(repositoryRoot, baseRevision, path));
    }

    private static IEnumerable<string> ReadNulPaths(string path)
    {
        var text = StrictUtf8.GetString(File.ReadAllBytes(path));
        var fields = text.Split('\0');
        for (var index = 0; index < fields.Length; index++)
        {
            if (fields[index].Length != 0)
            {
                yield return fields[index];
            }
            else if (index != fields.Length - 1)
            {
                throw new FormatException("Scribe changed-path manifest contains an empty path.");
            }
        }
    }

    private static IEnumerable<string> ReadLines(string path)
    {
        var text = StrictUtf8.GetString(File.ReadAllBytes(path));
        foreach (var line in text.Split('\n'))
        {
            var value = line.TrimEnd('\r');
            if (value.Length != 0) yield return value;
        }
    }

    private static void ValidateBase(string repositoryRoot, string baseRevision)
    {
        var result = RunGit(repositoryRoot, ["cat-file", "-e", $"{baseRevision}^{{commit}}"]);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException("Scribe delta base commit is unavailable in git.");
        }
    }

    internal static void ValidateChangeManifest(
        string repositoryRoot,
        string baseRevision,
        RawChangeSet declared)
    {
        var tracked = RunGit(
            repositoryRoot,
            ["diff", "--name-only", "--no-renames", "-z", baseRevision, "--"],
            maximumOutputBytes: 16 * 1024 * 1024);
        var untracked = RunGit(
            repositoryRoot,
            ["ls-files", "--others", "--exclude-standard", "-z"],
            maximumOutputBytes: 16 * 1024 * 1024);
        if (tracked.ExitCode != 0 || untracked.ExitCode != 0)
        {
            throw new InvalidOperationException("Scribe candidate delta cannot be derived from git.");
        }

        var expected = ReadNulPaths(tracked.StandardOutput)
            .Concat(ReadNulPaths(untracked.StandardOutput))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var actual = declared.Paths
            .Select(static path => path.Value)
            .ToImmutableHashSet(StringComparer.Ordinal);
        if (!expected.SetEquals(actual))
        {
            throw new FormatException(
                "Scribe changed-path manifest does not match the git candidate delta.");
        }
    }

    internal static void ValidateProducerManifest(
        string repositoryRoot,
        ImmutableHashSet<string> declared)
    {
        var script = Path.Combine(
            repositoryRoot,
            "tools",
            "scripts",
            "report",
            "lean-report-input.sh");
        var result = BoundedProcessRunner.Run(
            "bash",
            [script, "scribe-producer-paths", "--repository", repositoryRoot],
            repositoryRoot,
            TimeSpan.FromMinutes(2),
            16 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "canonical Scribe producer closure is unavailable: "
                + StrictUtf8.GetString(result.StandardError).Trim());
        }

        var expected = ParseProducerPaths(ReadLines(result.StandardOutput));
        if (!expected.SetEquals(declared))
        {
            throw new FormatException(
                "Scribe producer-path manifest does not match the canonical derived closure.");
        }
    }

    private static ImmutableHashSet<string> ParseProducerPaths(IEnumerable<string> paths)
    {
        var result = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (!RepoPath.TryCreate(path, out var parsed) || !result.Add(parsed.Value))
            {
                throw new FormatException(
                    $"Scribe producer closure contains an invalid or duplicate path: {path}");
            }
        }

        return result.Count > 0
            ? result.ToImmutable()
            : throw new FormatException("Scribe producer closure is empty.");
    }

    private static string? ReadBaseDocument(
        string repositoryRoot,
        string baseRevision,
        string path)
    {
        var objectName = $"{baseRevision}:{path}";
        var type = RunGit(repositoryRoot, ["cat-file", "-t", objectName]);
        if (type.ExitCode != 0) return null;
        if (!string.Equals(StrictUtf8.GetString(type.StandardOutput).Trim(), "blob", StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"trusted base Scribe emission is not a blob: {path}");
        }

        var result = RunGit(repositoryRoot, ["show", objectName], maximumOutputBytes: 16 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException($"trusted base Scribe emission cannot be read: {path}");
        }

        return StrictUtf8.GetString(result.StandardOutput);
    }

    private static ProcessOutput RunGit(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        int maximumOutputBytes = 64 * 1024) =>
        BoundedProcessRunner.Run(
            "git",
            arguments,
            repositoryRoot,
            TimeSpan.FromSeconds(30),
            maximumOutputBytes);

    private static IEnumerable<string> ReadNulPaths(byte[] bytes)
    {
        var fields = StrictUtf8.GetString(bytes).Split('\0');
        for (var index = 0; index < fields.Length; index++)
        {
            if (fields[index].Length != 0)
            {
                yield return fields[index];
            }
            else if (index != fields.Length - 1)
            {
                throw new FormatException("git emitted an empty changed path.");
            }
        }
    }

    private static IEnumerable<string> ReadLines(byte[] bytes)
    {
        foreach (var line in StrictUtf8.GetString(bytes).Split('\n'))
        {
            var value = line.TrimEnd('\r');
            if (value.Length != 0) yield return value;
        }
    }
}
