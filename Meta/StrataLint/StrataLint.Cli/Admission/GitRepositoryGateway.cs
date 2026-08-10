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
        TimeSpan timeout);
}

internal sealed class ProductionGitProcessRunner : IGitProcessRunner
{
    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout) =>
        BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            64 * 1024 * 1024);
}

internal sealed partial class GitRepositoryGateway : IRepositoryGateway
{
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

        // 「旧侧」有两个不同的问题,须用两个不同的提交回答,不可合并成一个:
        //
        //   Revision —— 「候选在扩展哪个受保护状态?」答案只能是 protected base 本身。
        //       准入的旧侧快照由它解出,而 CI 恰恰也从同一个 pull_request.base.sha
        //       产出 --baseline-lean-report。二者必须是同一棵树,否则同一份 report
        //       被要求同时是两棵树的 report,报出 INFRASTRUCTURE_FAILURE(PR #1144)。
        //
        //   changeBase —— 「候选自己改了什么?」答案是 merge-base。dev 在候选在飞
        //       期间前进时,protected base 不再是候选祖先,拿它做 diff 会把 dev 的
        //       改动反向记到候选头上(候选看起来在删除 dev 刚加的东西)。
        //
        // 此前二者共用一个变量。strict 分支保护强制 merge-base == base.sha,使这个
        // 混同不可观测;strict 已按 τ=0 裁决永久关闭(CLAUDE.md 第 19 条),混同随即
        // 成为常态失败,故在此把两个角色拆开。
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

        var paths = ParseChangedPaths(GitBytes(
                "diff",
                "--name-status",
                "-z",
                "-M",
                "-C",
                "--find-copies-harder",
                changeBase,
                "--"))
            .Concat(ParseNulStrings(GitBytes("ls-files", "--others", "--exclude-standard", "-z")))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        return new PreparedRepository(revision, changeBase, RawChangeSet.Create(paths));
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

    // 冻结账本切换成一节点一文件后,它不再是单个 blob 而是一个目录。
    // 与 ReadRevisionFile 同样的严格性:只接受常规 blob,路径必须落在给定前缀下。
    internal ImmutableArray<RawRepositoryEntry> ReadRevisionFilesUnder(string revision, string prefix)
    {
        if (!IsObjectId(revision))
        {
            throw new InvalidOperationException("revision tree read requires an exact commit OID");
        }

        RequireObjectType(revision, "commit");
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var entry in ParseTree(GitBytes("ls-tree", "-r", "-z", revision, "--", prefix)))
        {
            if (entry.Mode is not ("100644" or "100755") || entry.ObjectType != "blob")
            {
                throw new InvalidOperationException(
                    $"revision file is not regular: {entry.Path} ({entry.Mode} {entry.ObjectType})");
            }

            entries.Add(new RawRepositoryEntry(
                entry.Path,
                ImmutableArray.CreateRange(GitBytes("show", $"{revision}:{entry.Path}"))));
        }

        return entries.ToImmutable();
    }

    internal RawRepositoryEntry ReadRevisionFile(string revision, string path)
    {
        if (!IsObjectId(revision))
        {
            throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.InvalidReference,
                "revision file read requires an exact commit OID");
        }
        RequireObjectType(revision, "commit");

        if (!RepoPath.TryCreate(path, out _))
        {
            throw new ArgumentException("revision file path is invalid", nameof(path));
        }

        var matches = ParseTree(GitBytes("ls-tree", "-z", revision, "--", path)).ToArray();
        if (matches.Length != 1 || !string.Equals(matches[0].Path, path, StringComparison.Ordinal))
        {
            throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.MissingObject,
                $"revision file is missing: {path}");
        }

        var entry = matches[0];
        if (entry.Mode is not ("100644" or "100755") || entry.ObjectType != "blob")
        {
            throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.WrongObjectType,
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
        var commandArguments = arguments.ToArray();
        ProcessOutput result;
        try
        {
            result = processRunner.Run(gitExecutable, commandArguments, root, gitTimeout);
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
