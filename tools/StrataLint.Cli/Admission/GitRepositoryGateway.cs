using System.Collections.Immutable;
using System.ComponentModel;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface IGitProcessRunner
{
    ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
        ReadOnlyMemory<byte> standardInput = default);
}

internal sealed class ProductionGitProcessRunner : IGitProcessRunner
{
    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
        ReadOnlyMemory<byte> standardInput = default) =>
        BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            maximumOutputBytes,
            standardInput);
}

internal sealed partial class GitRepositoryGateway : IRepositoryGateway
{
    internal const int DefaultGitOutputBytes = 64 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly string root;
    private readonly IGitProcessRunner processRunner;
    private readonly string gitExecutable;
    private readonly TimeSpan gitTimeout;

    internal GitRepositoryGateway(string root)
        : this(root, new ProductionGitProcessRunner(), "git", TimeSpan.FromSeconds(120))
    {
    }

    internal GitRepositoryGateway(
        string root,
        IGitProcessRunner processRunner,
        string gitExecutable)
        : this(root, processRunner, gitExecutable, TimeSpan.FromSeconds(120))
    {
    }

    internal GitRepositoryGateway(
        string root,
        IGitProcessRunner processRunner,
        string gitExecutable,
        TimeSpan gitTimeout)
    {
        this.root = Path.GetFullPath(root);
        this.processRunner = processRunner ?? throw new ArgumentNullException(nameof(processRunner));
        this.gitExecutable = string.IsNullOrWhiteSpace(gitExecutable)
            ? throw new ArgumentException("Git executable is required", nameof(gitExecutable))
            : gitExecutable;
        this.gitTimeout = gitTimeout > TimeSpan.Zero
            ? gitTimeout
            : throw new ArgumentOutOfRangeException(nameof(gitTimeout));
    }

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
                "clean checkout requires --protected-base; candidate HEAD cannot protect itself");
        }

        // 「旧侧」有两个不同的问题,不可先验地合并成一个:
        //
        //   Revision —— 「候选在扩展哪个受保护状态?」答案只能是 protected base 本身。
        //       准入的旧侧快照由它解出;旧侧 Lean 已不参与 admission。
        //
        //   changeBase —— 「受审树相对其 dev 状态净改了什么?」CI checkout
        //       refs/pull/N/merge,并把该 merge commit 的第一父提交作为 protected base,
        //       故 CI 中 changeBase == Revision,而 diff(HEAD^1, HEAD) 正是落地净增量。
        //
        // 下方 merge-base fallback 只服务本地 dirty/preflight 调用者:若它显式传入的
        // protected base 不是 HEAD 祖先,仍须隔离调用者自己的净改动。它不是 CI 的
        // PR delta 定义;CI 的两个地址由同一个 GitHub merge 对象机械绑定。
        var changeBase = revision;
        var ancestor = GitRaw(new[] { "merge-base", "--is-ancestor", revision, head }, allowNonzero: true);
        if (ancestor.ExitCode != 0)
        {
            changeBase = GitText("merge-base", revision, head).Trim();
        }

        if (!dirty && revision == head)
        {
            throw new InvalidOperationException(
                "protected base equals clean candidate HEAD; history comparison would be vacuous");
        }

        return new PreparedRepository(revision, changeBase, ReadChanges(changeBase));
    }

    public RawChangeSet ReadCurrentChanges()
    {
        var head = GitText("rev-parse", "HEAD").Trim();
        return ReadChanges(head);
    }

    public RawChangeSet ReadChanges(string changeBase)
    {
        var changes = ParseChanges(GitBytes(
                "diff",
                "--name-status",
                "-z",
                "-M",
                "-C",
                "--find-copies-harder",
                changeBase,
                "--"))
            .Concat(ParseNulStrings(GitBytes("ls-files", "--others", "--exclude-standard", "-z"))
                .Select(static path => (Path: path, Kind: RawChangeKind.Added)))
            .GroupBy(static change => change.Path, StringComparer.Ordinal)
            .Select(static group => group
                .OrderBy(static change => ChangeKindPriority(change.Kind))
                .First())
            .OrderBy(static change => change.Path, StringComparer.Ordinal)
            .ToArray();
        return RawChangeSet.CreateWithKinds(changes);
    }

    private static int ChangeKindPriority(RawChangeKind kind) => kind switch
    {
        RawChangeKind.Deleted => 0,
        RawChangeKind.Added => 1,
        RawChangeKind.Modified => 2,
        RawChangeKind.Copied => 3,
        _ => throw new InvalidOperationException($"unsupported raw change kind: {kind}"),
    };

    public RawRepositorySnapshot ReadCurrent() => GitRepositorySnapshotReader.ReadCurrent(root);

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        var tree = ParseTree(GitBytes("ls-tree", "-r", "-l", "-z", revision)).ToArray();
        return RawRepositorySnapshot.Create(ReadTreeBlobs(
            tree,
            entry => $"protected base has non-regular entry {entry.Path} ({entry.Mode} {entry.ObjectType})"));
    }

    private IEnumerable<RawRepositoryEntry> ReadTreeBlobs(
        IReadOnlyList<TreeEntry> tree,
        Func<TreeEntry, string> invalidEntryMessage)
    {
        foreach (var entry in tree)
        {
            if (entry.Mode is not ("100644" or "100755")
                || entry.ObjectType != "blob"
                || entry.Size is null)
            {
                throw new InvalidOperationException(invalidEntryMessage(entry));
            }
        }

        var objects = tree
            .DistinctBy(static entry => entry.ObjectId, StringComparer.Ordinal)
            .ToArray();
        if (objects.Length == 0)
        {
            return [];
        }

        var input = StrictUtf8.GetBytes(
            string.Concat(objects.Select(static entry => entry.ObjectId + "\n")));
        var maximumOutputBytes = BatchOutputLimit(objects);
        var output = GitRaw(
                ["cat-file", "--batch"],
                allowNonzero: false,
                maximumOutputBytes: maximumOutputBytes,
                standardInput: input)
            .StandardOutput;
        var blobs = ParseBatchObjects(objects, output);
        return tree.Select(entry => new RawRepositoryEntry(
            entry.Path,
            blobs[entry.ObjectId],
            (entry.ObjectId.Length == 40 ? "git-sha1:" : "git-sha256:") + entry.ObjectId));
    }

    private static int BatchOutputLimit(IEnumerable<TreeEntry> entries)
    {
        long maximum = 0;
        foreach (var entry in entries)
        {
            var size = entry.Size!.Value;
            var overhead = entry.ObjectId.Length + 64;
            if (size > int.MaxValue || maximum > int.MaxValue - size - overhead)
            {
                throw new InvalidOperationException("revision snapshot exceeds the supported batch size");
            }

            maximum += size + overhead;
        }

        return (int)maximum;
    }

    private static IReadOnlyDictionary<string, ImmutableArray<byte>> ParseBatchObjects(
        IReadOnlyList<TreeEntry> expected,
        byte[] output)
    {
        var blobs = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal);
        var offset = 0;
        foreach (var entry in expected)
        {
            var headerEnd = Array.IndexOf(output, (byte)'\n', offset);
            if (headerEnd < offset)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var header = StrictUtf8.GetString(output.AsSpan(offset, headerEnd - offset));
            var fields = header.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            if (fields.Length != 3
                || !string.Equals(fields[0], entry.ObjectId, StringComparison.Ordinal)
                || !string.Equals(fields[1], "blob", StringComparison.Ordinal)
                || !long.TryParse(
                    fields[2],
                    System.Globalization.NumberStyles.None,
                    System.Globalization.CultureInfo.InvariantCulture,
                    out var size)
                || size != entry.Size
                || size > int.MaxValue)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var contentStart = headerEnd + 1;
            if (size > output.Length - contentStart - 1)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var contentEnd = contentStart + (int)size;
            if (output[contentEnd] != (byte)'\n')
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            blobs.Add(
                entry.ObjectId,
                ImmutableArray.CreateRange(output.AsSpan(contentStart, (int)size).ToArray()));
            offset = contentEnd + 1;
        }

        if (offset != output.Length)
        {
            throw new InvalidOperationException("git cat-file --batch emitted trailing data");
        }

        return blobs;
    }

    private static InvalidOperationException InvalidBatchOutput(string objectId) =>
        new($"git cat-file --batch emitted invalid data for object {objectId}");

    private IEnumerable<TreeEntry> ParseTree(byte[] bytes)
    {
        foreach (var entry in SplitNul(bytes))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0) throw new InvalidOperationException("git tree emitted invalid metadata");
            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab))
                .Split(' ', StringSplitOptions.RemoveEmptyEntries);
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length is not (3 or 4) || !RepoPath.TryCreate(path, out _))
            {
                throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
            }

            long? size = null;
            if (metadata.Length == 4 && metadata[3] != "-")
            {
                if (!long.TryParse(
                        metadata[3],
                        System.Globalization.NumberStyles.None,
                        System.Globalization.CultureInfo.InvariantCulture,
                        out var parsedSize))
                {
                    throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
                }

                size = parsedSize;
            }

            yield return new TreeEntry(metadata[0], metadata[1], metadata[2], path, size);
        }
    }

    private string GitText(params string[] arguments) => StrictUtf8.GetString(GitBytes(arguments));

    private byte[] GitBytes(params string[] arguments)
    {
        var result = GitRaw(arguments, allowNonzero: false);
        return result.StandardOutput;
    }

    private ProcessOutput GitRaw(
        IEnumerable<string> arguments,
        bool allowNonzero,
        int maximumOutputBytes = DefaultGitOutputBytes,
        ReadOnlyMemory<byte> standardInput = default)
    {
        var commandArguments = arguments.ToArray();
        ProcessOutput result;
        try
        {
            result = processRunner.Run(
                gitExecutable,
                commandArguments,
                root,
                gitTimeout,
                maximumOutputBytes,
                standardInput);
        }
        catch (TimeoutException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.Timeout,
                commandArguments,
                detail: exception.Message,
                exception: exception);
        }
        catch (Win32Exception exception)
        {
            throw InfrastructureFailure(
                exception.NativeErrorCode is 2 or 3
                    ? GitCommandFailureKind.ExecutableNotFound
                    : GitCommandFailureKind.Process,
                commandArguments,
                nativeErrorCode: exception.NativeErrorCode,
                detail: exception.Message,
                exception: exception);
        }
        catch (IOException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.Io,
                commandArguments,
                detail: exception.Message,
                exception: exception);
        }
        catch (UnauthorizedAccessException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.Io,
                commandArguments,
                detail: exception.Message,
                exception: exception);
        }
        catch (InvalidOperationException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.Process,
                commandArguments,
                detail: exception.Message,
                exception: exception);
        }

        if (!allowNonzero && result.ExitCode != 0)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.NonzeroExit,
                commandArguments,
                exitCode: result.ExitCode,
                standardError: DecodeFailureText(result.StandardError));
        }

        return result;
    }

    private GitInfrastructureException InfrastructureFailure(
        GitCommandFailureKind kind,
        IReadOnlyList<string> arguments,
        int? exitCode = null,
        int? nativeErrorCode = null,
        string standardError = "",
        string detail = "",
        Exception? exception = null) =>
        new(
            new GitCommandFailure(
                kind,
                gitExecutable,
                arguments.ToImmutableArray(),
                exitCode,
                nativeErrorCode,
                standardError,
                detail),
            exception);

    private static string DecodeFailureText(byte[] bytes) =>
        Encoding.UTF8.GetString(bytes).Trim();

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

    private static IEnumerable<(string Path, RawChangeKind Kind)> ParseChanges(byte[] bytes)
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

            if (status[0] == 'R')
            {
                yield return (fields[index++], RawChangeKind.Deleted);
                yield return (fields[index++], RawChangeKind.Added);
                continue;
            }

            if (status[0] == 'C')
            {
                yield return (fields[index++], RawChangeKind.Copied);
                yield return (fields[index++], RawChangeKind.Added);
                continue;
            }

            var path = fields[index++];
            yield return (path, status[0] switch
            {
                'A' => RawChangeKind.Added,
                'D' => RawChangeKind.Deleted,
                _ => RawChangeKind.Modified,
            });
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

    private sealed record TreeEntry(
        string Mode,
        string ObjectType,
        string ObjectId,
        string Path,
        long? Size);
}
