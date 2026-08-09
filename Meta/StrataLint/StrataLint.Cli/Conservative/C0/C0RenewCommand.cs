using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record C0RenewState(
    FrozenRevisionIdentity Base,
    FrozenRevisionIdentity Preimage,
    ImmutableArray<string> ChangedPaths,
    RepositorySnapshot Snapshot);

internal sealed record C0RenewGateResult(
    int ExitCode,
    ImmutableArray<byte> Output,
    ImmutableArray<byte> Error);

internal interface IC0RenewEnvironment
{
    C0RenewState ReadState(string baseReference);

    C0RenewGateResult RunConservativeGate(
        string exactBaseCommit,
        string exactPreimageCommit);

}

internal static class C0RenewCommand
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments) =>
        Run(arguments, new ProductionC0RenewEnvironment(repositoryRoot));

    internal static CommandResult Run(
        IReadOnlyList<string> arguments,
        IC0RenewEnvironment environment)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(environment);
        try
        {
            var baseReference = Parse(arguments);
            var initial = environment.ReadState(baseReference);
            RequireSha1(initial);
            if (!initial.ChangedPaths.IsEmpty)
            {
                throw new InvalidOperationException(
                    "C0 verification requires a clean committed preimage");
            }

            if (!initial.Snapshot.TryGetFile(RepositoryRules.TowerManifestPath, out var tower))
            {
                throw new InvalidOperationException("TOWER is missing");
            }
            var members = C0TowerProjection.ReadMembers(tower.RawBytes.AsSpan());
            if (!C0CeremonyProjection.TrustRootMatchesSnapshot(
                    members,
                    initial.Snapshot,
                    out var mismatch))
            {
                throw new InvalidOperationException(mismatch);
            }

            var gate = environment.RunConservativeGate(
                initial.Base.Revision,
                initial.Preimage.Revision);
            if (gate.ExitCode != 0)
            {
                throw new InvalidOperationException(
                    "the conservative gate did not produce a renewable certificate"
                    + GateDetail(gate));
            }

            return Success();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"C0_VERIFY_FAILED [{exception.GetType().Name}] {exception.Message}\n"
                + (exception.InnerException is { } inner
                    ? $"C0_VERIFY_FAILED_INNER [{inner.GetType().Name}] {inner.Message}\n"
                    : string.Empty));
        }
    }

    private static void RequireSha1(C0RenewState state)
    {
        if (state.Base.Revision.Length != 40
            || state.Preimage.Revision.Length != 40
            || !state.Base.CommitOid.StartsWith("git-sha1:", StringComparison.Ordinal)
            || !state.Base.TreeOid.StartsWith("git-sha1:", StringComparison.Ordinal)
            || !state.Preimage.CommitOid.StartsWith("git-sha1:", StringComparison.Ordinal)
            || !state.Preimage.TreeOid.StartsWith("git-sha1:", StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "C0 renewal supports only the repository's canonical SHA-1 object format");
        }
    }

    private static string Parse(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || arguments[0] != "--base"
            || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new ArgumentException("USAGE: StrataLint c0-verify --base REV");
        }

        return arguments[1];
    }

    private static string GateDetail(C0RenewGateResult gate)
    {
        var error = StrictUtf8.GetString(gate.Error.AsSpan());
        var output = StrictUtf8.GetString(gate.Output.AsSpan());
        if (error.Length == 0 && output.Length == 0) return $" (exit {gate.ExitCode})";

        var separator = error.Length > 0
            && output.Length > 0
            && error[^1] != '\n'
                ? "\n"
                : string.Empty;
        return $" (exit {gate.ExitCode}: {error}{separator}{output})";
    }

    private static CommandResult Success() => new(
        true,
        "C0_VERIFIED changed_files=0 admission=not-evaluated\n",
        string.Empty);
}

internal sealed class ProductionC0RenewEnvironment : IC0RenewEnvironment
{
    internal const int LeanReportBudgetMinutes = 90;
    internal const int GitOperationBudgetMinutes = 10;

    private readonly string root;
    private readonly GitRepositoryGateway repository;

    internal ProductionC0RenewEnvironment(string root)
    {
        this.root = Path.GetFullPath(root);
        repository = new GitRepositoryGateway(this.root);
    }

    public C0RenewState ReadState(string baseReference)
    {
        var @base = repository.ResolveReference(baseReference);
        var preimage = repository.ResolveCurrentRevision();
        repository.RequireStrictAncestor(@base.Revision, preimage.Revision);
        return new C0RenewState(
            @base,
            preimage,
            repository.WorkingTreeChanges(),
            Decode(repository.ReadCurrent()));
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    public C0RenewGateResult RunConservativeGate(
        string exactBaseCommit,
        string exactPreimageCommit)
    {
        using var @base = C0RenewCandidateWorkspace.Materialize(
            root,
            exactBaseCommit);
        using var candidate = C0RenewCandidateWorkspace.Materialize(
            root,
            exactPreimageCommit);
        var candidateReport = Absolute(
            candidate.Root,
            ".lake/build/stratalint/raw-lean-report.json");
        var baselineReport = Absolute(
            @base.Root,
            ".lake/build/stratalint/raw-lean-report.json");
        RunRequired(
            "/bin/bash",
            [
                Absolute(@base.Root, C0CeremonyProjection.LeanReportPairPath),
                "--producer",
                Absolute(@base.Root, C0CeremonyProjection.LeanInspectorScriptPath),
                "--lake-bin",
                ResolveLakeExecutable(),
                "--candidate-root",
                candidate.Root,
                "--candidate-output",
                candidateReport,
                "--baseline-root",
                @base.Root,
                "--baseline-output",
                baselineReport,
            ],
            candidate.Root,
            TimeSpan.FromMinutes(LeanReportBudgetMinutes),
            "base-owned Lean report production failed");
        var result = BoundedProcessRunner.Run(
            "/usr/bin/env",
            [
                "CI=true",
                "/bin/bash",
                Absolute(@base.Root, C0CeremonyProjection.GateWiringPath),
                "--candidate",
                candidate.Root,
                "--judge-root",
                @base.Root,
                "--base",
                exactBaseCommit,
                "--candidate-lean-report",
                candidateReport,
                "--baseline-lean-report",
                baselineReport,
            ],
            @base.Root,
            TimeSpan.FromMinutes(LeanReportBudgetMinutes),
            64 * 1024 * 1024);
        return new C0RenewGateResult(
            result.ExitCode == 3 ? 0 : result.ExitCode,
            ImmutableArray.CreateRange(result.StandardOutput),
            ImmutableArray.CreateRange(result.StandardError));
    }

    private string Absolute(string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static void RunRequired(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        string failure)
    {
        var result = BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            64 * 1024 * 1024);
        if (result.ExitCode == 0) return;
        var error = new UTF8Encoding(false, true).GetString(result.StandardError).Trim();
        throw new InvalidOperationException(error.Length == 0 ? failure : error);
    }

    private static string ResolveLakeExecutable()
    {
        var configured = Environment.GetEnvironmentVariable("LAKE_BIN");
        if (!string.IsNullOrWhiteSpace(configured) && Path.IsPathFullyQualified(configured))
        {
            if (File.Exists(configured)) return Path.GetFullPath(configured);
            throw new InvalidOperationException("LAKE_BIN does not name an existing executable");
        }

        foreach (var directory in (Environment.GetEnvironmentVariable("PATH") ?? string.Empty)
                     .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
        {
            var candidate = Path.Combine(directory, "lake");
            if (File.Exists(candidate)) return Path.GetFullPath(candidate);
        }

        throw new InvalidOperationException("an absolute lake executable is required");
    }
}

internal sealed class C0RenewCandidateWorkspace : IDisposable
{
    private readonly string temporaryRoot;
    private bool disposed;

    private C0RenewCandidateWorkspace(string temporaryRoot, string root)
    {
        this.temporaryRoot = temporaryRoot;
        Root = root;
    }

    internal string Root { get; }

    internal static C0RenewCandidateWorkspace Materialize(
        string sourceRoot,
        string exactPreimageCommit)
    {
        var source = Path.GetFullPath(sourceRoot);
        var expected = new GitRepositoryGateway(source).ResolveFrozenRevision(
            exactPreimageCommit);
        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-c0-renew-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var candidate = Path.Combine(temporary, "candidate");
            RunGit(
                source,
                ["clone", "--no-checkout", "--quiet", "--shared", "--", source, candidate],
                "could not clone the C0 preimage");
            RunGit(
                candidate,
                ["checkout", "--detach", "--quiet", exactPreimageCommit],
                "could not check out the C0 preimage");
            var repository = new GitRepositoryGateway(candidate);
            var actual = repository.ResolveCurrentRevision();
            if (actual != expected)
            {
                throw new InvalidOperationException(
                    "materialized C0 gate candidate does not match the frozen preimage");
            }

            if (!repository.WorkingTreeChanges().IsDefaultOrEmpty)
            {
                throw new InvalidOperationException(
                    "materialized C0 gate candidate is not clean");
            }

            return new C0RenewCandidateWorkspace(temporary, candidate);
        }
        catch
        {
            Directory.Delete(temporary, recursive: true);
            throw;
        }
    }

    public void Dispose()
    {
        if (disposed) return;
        disposed = true;
        Directory.Delete(temporaryRoot, recursive: true);
    }

    private static void RunGit(
        string workingDirectory,
        IReadOnlyList<string> arguments,
        string failure)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            arguments,
            workingDirectory,
            TimeSpan.FromMinutes(ProductionC0RenewEnvironment.GitOperationBudgetMinutes),
            64 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            var error = StrictUtf8(result.StandardError).Trim();
            throw new InvalidOperationException(error.Length == 0 ? failure : error);
        }
    }

    private static string StrictUtf8(byte[] bytes) =>
        new UTF8Encoding(false, true).GetString(bytes);
}
