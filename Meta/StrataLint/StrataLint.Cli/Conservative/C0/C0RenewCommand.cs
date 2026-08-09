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
        // One ceremony budget spans both children, not one budget each. Handing
        // LeanReportBudgetMinutes to the report producer and again to the gate lets a slow
        // first child leave the second with a full fresh allowance, so the pair can run to
        // twice the budget the ceremony is supposed to have. Start the clock here and give
        // the second child only what is left.
        var reportBudgetClock = System.Diagnostics.Stopwatch.StartNew();
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
            RemainingReportBudget(reportBudgetClock),
            64 * 1024 * 1024);
        return new C0RenewGateResult(
            result.ExitCode == 3 ? 0 : result.ExitCode,
            ImmutableArray.CreateRange(result.StandardOutput),
            ImmutableArray.CreateRange(result.StandardError));
    }

    /// Unlike the Lean cache, which is an optimisation and degrades to a cold build, an
    /// exhausted budget is a real outcome: continuing would mean the ceremony ran past the
    /// window it was granted. Fail closed, and name the budget that ran out -- otherwise the
    /// eventual timeout surfaces as whichever inner step happened to be running, pointing at
    /// the symptom instead of at the ceremony budget (the shape #993 records).
    /// Elapsed time comes from a Stopwatch rather than a wall clock: this measures how much
    /// of the budget the first child consumed, and a monotonic source keeps that measurement
    /// correct across a clock adjustment mid-ceremony. DateTimeOffset.UtcNow is also a banned
    /// symbol here (RS0030, "inject a clock or pass an explicit deterministic timestamp").
    private static TimeSpan RemainingReportBudget(System.Diagnostics.Stopwatch elapsed)
    {
        var remaining = TimeSpan.FromMinutes(LeanReportBudgetMinutes) - elapsed.Elapsed;
        if (remaining <= TimeSpan.Zero)
        {
            throw new InvalidOperationException(
                "C0_RENEW_BUDGET_EXHAUSTED owner=lean-report-budget stage=gate-wiring " +
                $"budget_minutes={LeanReportBudgetMinutes}");
        }

        return remaining;
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

            // Seed the Lean build cache from a donor tree instead of starting empty. Both
            // workspaces this method produces otherwise rebuild mathlib and D5 from nothing,
            // which is the pair of cache-empty materializations #972 records; each .lake is
            // roughly the size of a worktree, and two of them once exhausted the disk and
            // took the live Lean report with them (#971).
            //
            // Placed after the revision and working-tree checks on purpose: clean-preimage is
            // a Git-level property (ChangedPaths, ResolveCurrentRevision, WorkingTreeChanges)
            // and .lake is gitignored, so seeding it afterwards is invisible to all three.
            // make worktree already copies a donor .lake for every lane in this repository.
            //
            // Provision falls back to `lake exe cache get` when no donor qualifies, so a
            // missing or mismatched donor degrades to the previous behaviour rather than failing.
            SeedLeanCache(source, exactPreimageCommit, candidate);

            return new C0RenewCandidateWorkspace(temporary, candidate);
        }
        catch
        {
            Directory.Delete(temporary, recursive: true);
            throw;
        }
    }

    /// The cache is an optimisation, never a correctness input: the ceremony's verdict comes
    /// from the frozen preimage and the reports built inside it, not from where the build
    /// artifacts came from. So a failure here must not abort a renew that would otherwise
    /// succeed -- it costs a cold build, which is exactly the status quo before this seeding
    /// existed. Any other choice would make an optimisation able to fail a trust-root ceremony.
    private static void SeedLeanCache(
        string sourceRoot,
        string exactPreimageCommit,
        string candidateRoot)
    {
        var clock = System.Diagnostics.Stopwatch.StartNew();
        try
        {
            var runner = new ProductionWorktreeProcessRunner();
            var pins = LeanPinSet.ReadBase(sourceRoot, exactPreimageCommit, runner);
            var donor = GitWorktreeInventory.SelectDonor(sourceRoot, pins, runner);
            var provisioned = LeanCacheProvisioner.Provision(donor, candidateRoot, runner);
            var warning = provisioned.Warning is null ? string.Empty : $" warning={provisioned.Warning}";
            // cache_state distinguishes the two regimes #972 asks to be recorded as D5 grows:
            // "donor" reused an existing .lake, anything else started from an empty one. Emitting
            // it alongside the elapsed seconds and the free disk is what turns "c0-renew felt
            // slow" into a series that can be compared across commits; without the state the
            // timings are two populations averaged into one meaningless number.
            Console.Out.WriteLine(
                $"C0_RENEW_LEAN_CACHE root={candidateRoot} strategy={provisioned.Strategy} " +
                $"method={provisioned.Method} cache_state={CacheState(provisioned.Strategy)} " +
                $"elapsed_seconds={clock.Elapsed.TotalSeconds:F1} " +
                $"disk_free_gb={DiskFreeGb(candidateRoot)}{warning}");
        }
        catch (Exception failure) when (failure is not OutOfMemoryException)
        {
            Console.Out.WriteLine(
                $"C0_RENEW_LEAN_CACHE root={candidateRoot} strategy=unavailable cache_state=cold " +
                $"elapsed_seconds={clock.Elapsed.TotalSeconds:F1} " +
                $"disk_free_gb={DiskFreeGb(candidateRoot)} detail={failure.Message}");
        }
    }

    /// "warm" only when an existing .lake was reused; every other strategy -- cache-get, or a
    /// failure that leaves the tree bare -- starts the Lean build from nothing and belongs to
    /// the cold population. Keeping the two apart is the point of recording at all.
    private static string CacheState(string strategy) =>
        string.Equals(strategy, "donor", StringComparison.Ordinal) ? "warm" : "cold";

    /// Free space on the volume holding the workspace. #972's failure mode was disk, not time:
    /// two cache-empty materializations once exhausted it and took the live Lean report down
    /// with them, so the series needs the headroom next to the duration.
    private static string DiskFreeGb(string path)
    {
        try
        {
            var root = Path.GetPathRoot(Path.GetFullPath(path));
            if (string.IsNullOrEmpty(root)) return "unknown";
            var drive = new DriveInfo(root);
            return (drive.AvailableFreeSpace / 1024d / 1024d / 1024d).ToString(
                "F1",
                System.Globalization.CultureInfo.InvariantCulture);
        }
        catch (Exception failure) when (failure is ArgumentException or IOException or UnauthorizedAccessException)
        {
            return "unknown";
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
