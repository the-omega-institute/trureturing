using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway : IRepositoryGateway
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly string root;

    internal GitRepositoryGateway(string root) => this.root = Path.GetFullPath(root);

    public AdmissionTopologyOutcome InspectAdmissionTopology()
    {
        var (defaultBranch, defaultHead) = ParseRemoteDefaultHead(
            GitText("ls-remote", "--symref", "origin", "HEAD"));
        var commit = GitRaw(new[] { "cat-file", "-e", $"{defaultHead}^{{commit}}" }, allowNonzero: true);
        if (commit.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"origin/{defaultBranch} at {defaultHead} is not available locally; fetch the default branch before topology verification");
        }

        var workflowObject = $"{defaultHead}:{AdmissionWorkflowTopology.WorkflowPath}";
        var objectType = GitRaw(new[] { "cat-file", "-t", workflowObject }, allowNonzero: true);
        if (objectType.ExitCode != 0
            || !string.Equals(
                StrictUtf8.GetString(objectType.StandardOutput).Trim(),
                "blob",
                StringComparison.Ordinal))
        {
            return new AdmissionTopologyOutcome.BootstrapNotActive(defaultBranch);
        }

        var workflow = GitBytes("cat-file", "blob", workflowObject);
        return AdmissionWorkflowTopology.HasRequiredBaseGate(workflow, defaultBranch)
            ? new AdmissionTopologyOutcome.SteadyStateActive(defaultBranch)
            : new AdmissionTopologyOutcome.BootstrapNotActive(defaultBranch);
    }

    public PreparedRepository Prepare(string? protectedBase)
    {
        var head = GitText("rev-parse", "HEAD").Trim();
        var dirty = GitText("status", "--porcelain", "--untracked-files=all").Length > 0;
        string revision;
        if (protectedBase is not null)
        {
            revision = GitText("rev-parse", "--verify", $"{protectedBase}^{{commit}}").Trim();
        }
        else if (dirty)
        {
            revision = head;
        }
        else
        {
            throw new InvalidOperationException(
                "clean checkout requires --protected-base/--merge-base; candidate HEAD cannot protect itself");
        }

        var ancestor = GitRaw(new[] { "merge-base", "--is-ancestor", revision, head }, allowNonzero: true);
        if (ancestor.ExitCode != 0)
        {
            throw new InvalidOperationException("protected base is not an ancestor of candidate HEAD");
        }

        if (!dirty && revision == head)
        {
            throw new InvalidOperationException(
                "protected base equals clean candidate HEAD; history comparison would be vacuous");
        }

        var paths = ParseChangedPaths(GitBytes(
                "diff",
                "--name-status",
                "-z",
                "-M",
                "-C",
                "--find-copies-harder",
                revision,
                "--"))
            .Concat(ParseNulStrings(GitBytes("ls-files", "--others", "--exclude-standard", "-z")))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        return new PreparedRepository(revision, RawChangeSet.Create(paths));
    }

    public RawRepositorySnapshot ReadCurrent() => GitRepositorySnapshotReader.ReadCurrent(root);

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var entry in ParseTree(GitBytes("ls-tree", "-r", "-z", revision)))
        {
            if (entry.Mode is not ("100644" or "100755") || entry.ObjectType != "blob")
            {
                throw new InvalidOperationException(
                    $"protected base has non-regular entry {entry.Path} ({entry.Mode} {entry.ObjectType})");
            }

            var bytes = GitBytes("show", $"{revision}:{entry.Path}");
            entries.Add(new RawRepositoryEntry(entry.Path, ImmutableArray.CreateRange(bytes)));
        }

        return RawRepositorySnapshot.Create(entries);
    }

    internal RawRepositoryEntry ReadRevisionFile(string revision, string path)
    {
        if (!IsObjectId(revision))
        {
            throw new InvalidOperationException("revision file read requires an exact commit OID");
        }

        if (!RepoPath.TryCreate(path, out _))
        {
            throw new ArgumentException("revision file path is invalid", nameof(path));
        }

        var matches = ParseTree(GitBytes("ls-tree", "-z", revision, "--", path)).ToArray();
        if (matches.Length != 1 || !string.Equals(matches[0].Path, path, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"revision file is missing: {path}");
        }

        var entry = matches[0];
        if (entry.Mode is not ("100644" or "100755") || entry.ObjectType != "blob")
        {
            throw new InvalidOperationException(
                $"revision file is not regular: {path} ({entry.Mode} {entry.ObjectType})");
        }

        return new RawRepositoryEntry(
            path,
            ImmutableArray.CreateRange(GitBytes("show", $"{revision}:{path}")));
    }

    private IEnumerable<TreeEntry> ParseTree(byte[] bytes)
    {
        foreach (var entry in SplitNul(bytes))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0) throw new InvalidOperationException("git tree emitted invalid metadata");
            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab)).Split(' ');
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length != 3 || !RepoPath.TryCreate(path, out _))
            {
                throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
            }

            yield return new TreeEntry(metadata[0], metadata[1], metadata[2], path);
        }
    }

    private string GitText(params string[] arguments) => StrictUtf8.GetString(GitBytes(arguments));

    private byte[] GitBytes(params string[] arguments)
    {
        var result = GitRaw(arguments, allowNonzero: false);
        return result.StandardOutput;
    }

    private ProcessOutput GitRaw(IEnumerable<string> arguments, bool allowNonzero)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromSeconds(120),
            64 * 1024 * 1024);
        if (!allowNonzero && result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git command failed");
        }

        return result;
    }

    private static IEnumerable<string> ParseNulStrings(byte[] bytes) =>
        SplitNul(bytes).Select(static item => StrictUtf8.GetString(item));

    private static (string DefaultBranch, string Head) ParseRemoteDefaultHead(string output)
    {
        const string branchPrefix = "ref: refs/heads/";
        string? defaultBranch = null;
        string? defaultHead = null;
        foreach (var rawLine in output.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            var fields = rawLine.TrimEnd('\r').Split('\t');
            if (fields.Length != 2 || !string.Equals(fields[1], "HEAD", StringComparison.Ordinal))
            {
                continue;
            }

            if (fields[0].StartsWith(branchPrefix, StringComparison.Ordinal))
            {
                defaultBranch = fields[0][branchPrefix.Length..];
            }
            else if (IsObjectId(fields[0]))
            {
                defaultHead = fields[0];
            }
        }

        if (string.IsNullOrEmpty(defaultBranch) || defaultHead is null)
        {
            throw new InvalidOperationException("origin HEAD did not identify one default branch and content address");
        }

        return (defaultBranch, defaultHead);
    }

    private static bool IsObjectId(string value) =>
        value.Length is 40 or 64 && value.All(char.IsAsciiHexDigit);

    private static IEnumerable<string> ParseChangedPaths(byte[] bytes)
    {
        var fields = SplitNul(bytes).Select(static item => StrictUtf8.GetString(item)).ToArray();
        for (var index = 0; index < fields.Length;)
        {
            var status = fields[index++];
            var pathCount = status.Length > 0 && status[0] is 'R' or 'C' ? 2 : 1;
            if (!ValidStatus(status) || index + pathCount > fields.Length)
            {
                throw new InvalidOperationException("git diff emitted invalid name-status metadata");
            }

            for (var pathIndex = 0; pathIndex < pathCount; pathIndex++)
            {
                yield return fields[index++];
            }
        }
    }

    private static bool ValidStatus(string status) => status switch
    {
        "A" or "M" or "D" or "T" or "U" or "X" or "B" => true,
        _ when status.Length > 1
            && status[0] is 'R' or 'C'
            && status.AsSpan(1).IndexOfAnyExceptInRange('0', '9') < 0 => true,
        _ => false,
    };

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index <= bytes.Length; index++)
        {
            if (index != bytes.Length && bytes[index] != 0) continue;
            if (index > start) yield return bytes[start..index];
            start = index + 1;
        }
    }

    private sealed record TreeEntry(string Mode, string ObjectType, string ObjectId, string Path);
}
