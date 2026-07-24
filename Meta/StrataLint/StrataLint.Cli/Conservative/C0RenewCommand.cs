using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record C0RenewState(
    FrozenRevisionIdentity Base,
    FrozenRevisionIdentity Preimage,
    RepositorySnapshot PreimageSnapshot,
    ImmutableArray<string> ChangedPaths,
    ImmutableArray<byte> CurrentTower,
    ImmutableArray<byte> CurrentCertificate);

internal sealed record C0RenewGateResult(
    int ExitCode,
    ImmutableArray<byte> Output,
    ImmutableArray<byte> Error);

internal sealed record C0RenewOutput(
    ImmutableArray<byte> TowerBytes,
    ImmutableArray<byte> CertificateBytes);

internal interface IC0RenewEnvironment
{
    C0RenewState ReadState(string baseReference);

    C0RenewGateResult RunConservativeGate(
        string exactBaseCommit,
        string exactPreimageCommit);

    IDisposable AcquireInstallLock();

    void Install(C0RenewOutput output);
}

internal static class C0RenewCommand
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly ImmutableHashSet<string> OutputPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            RepositoryRules.TowerManifestPath,
            C0CeremonyProjection.CertificatePath);

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
            var dirty = initial.ChangedPaths.ToImmutableHashSet(StringComparer.Ordinal);
            if (!dirty.IsSubsetOf(OutputPaths))
            {
                throw new InvalidOperationException(
                    "C0 renewal requires a clean committed preimage; only prior C0 outputs may differ");
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

            var certificate = ExtractCertificate(gate.Output, initial);
            var output = Materialize(initial, certificate);
            using var installLock = environment.AcquireInstallLock();
            var confirmed = environment.ReadState(baseReference);
            RequireUnchanged(initial, confirmed);
            var changedFiles = 0;
            if (!output.CertificateBytes.AsSpan().SequenceEqual(initial.CurrentCertificate.AsSpan()))
            {
                changedFiles++;
            }

            if (!output.TowerBytes.AsSpan().SequenceEqual(initial.CurrentTower.AsSpan()))
            {
                changedFiles++;
            }

            if (changedFiles > 0) environment.Install(output);
            return Success(changedFiles);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"C0_RENEW_FAILED {exception.Message}\n");
        }
    }

    private static C0RenewOutput Materialize(
        C0RenewState state,
        ImmutableArray<byte> certificate)
    {
        ValidateCertificate(certificate, state);
        if (!state.PreimageSnapshot.TryGetFile(RepositoryRules.TowerManifestPath, out var tower))
        {
            throw new InvalidOperationException(
                $"committed preimage is missing {RepositoryRules.TowerManifestPath}");
        }

        var identity = new C0CeremonyIdentity(
            state.Base.Revision,
            state.Preimage.Revision,
            Untag(state.Preimage.TreeOid, "git-sha1:"));
        var members = C0CeremonyProjection.CreateMembers(
            state.PreimageSnapshot,
            certificate.AsSpan(),
            identity);
        var towerBytes = C0TowerProjection.Write(tower.RawBytes.AsSpan(), members);
        return new C0RenewOutput(towerBytes, certificate);
    }

    private static ImmutableArray<byte> ExtractCertificate(
        ImmutableArray<byte> gateOutput,
        C0RenewState state)
    {
        var text = StrictUtf8.GetString(gateOutput.AsSpan());
        var matches = new List<ImmutableArray<byte>>();
        foreach (var line in text.Split('\n'))
        {
            if (!line.StartsWith('{')) continue;
            try
            {
                using var document = JsonDocument.Parse(line);
                if (document.RootElement.TryGetProperty("schema", out var schema)
                    && schema.GetString() == ConservativeExtensionVerifier.CertificateSchema)
                {
                    matches.Add(ImmutableArray.CreateRange(StrictUtf8.GetBytes(line + "\n")));
                }
            }
            catch (JsonException)
            {
                // Other gate output remains diagnostics, not a certificate candidate.
            }
        }

        if (matches.Count != 1)
        {
            throw new InvalidOperationException(
                $"conservative gate emitted {matches.Count} certificate candidates");
        }

        var certificate = matches[0];
        ValidateCertificate(certificate, state);
        return certificate;
    }

    private static void ValidateCertificate(
        ImmutableArray<byte> certificate,
        C0RenewState state)
    {
        using var document = JsonDocument.Parse(certificate.ToArray());
        var root = document.RootElement;
        if (root.GetProperty("schema").GetString()
                != ConservativeExtensionVerifier.CertificateSchema
            || root.GetProperty("status").GetString() != "CORPUS_CONSERVATIVE"
            || root.GetProperty("findings").GetArrayLength() != 0)
        {
            throw new InvalidOperationException(
                "the conservative gate did not produce a renewable certificate");
        }

        var baseline = root.GetProperty("baseline");
        var candidate = root.GetProperty("candidate");
        if (baseline.GetProperty("commit_oid").GetString() != state.Base.Revision
            || baseline.GetProperty("tree_oid").GetString() != state.Base.TreeOid
            || candidate.GetProperty("commit_oid").GetString() != state.Preimage.Revision
            || candidate.GetProperty("tree_oid").GetString() != state.Preimage.TreeOid)
        {
            throw new InvalidOperationException(
                "conservative certificate identities do not match the frozen renewal inputs");
        }

        var implication = root.GetProperty("positive_implication");
        if (implication.GetProperty("baseline_admit_count").GetInt32()
            != implication.GetProperty("preserved_admit_count").GetInt32())
        {
            throw new InvalidOperationException(
                "conservative certificate does not preserve every baseline admit");
        }

        var canonical = StructuredCanonicalWriter.WriteJson(root);
        if (!canonical.AsSpan().SequenceEqual(certificate.AsSpan()))
        {
            throw new InvalidOperationException("conservative certificate bytes are not canonical");
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

    private static void RequireUnchanged(C0RenewState initial, C0RenewState confirmed)
    {
        if (confirmed.Base != initial.Base
            || confirmed.Preimage != initial.Preimage
            || !confirmed.ChangedPaths.SequenceEqual(
                initial.ChangedPaths,
                StringComparer.Ordinal)
            || !confirmed.CurrentTower.AsSpan().SequenceEqual(initial.CurrentTower.AsSpan())
            || !confirmed.CurrentCertificate.AsSpan().SequenceEqual(
                initial.CurrentCertificate.AsSpan()))
        {
            throw new InvalidOperationException("C0 renewal inputs changed while the gate was running");
        }
    }

    private static string Parse(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || arguments[0] != "--base"
            || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new ArgumentException("USAGE: StrataLint c0-renew --base REV");
        }

        return arguments[1];
    }

    private static string Untag(string value, string prefix)
    {
        if (!value.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"C0 identity is missing {prefix}");
        }

        return value[prefix.Length..];
    }

    private static string GateDetail(C0RenewGateResult gate)
    {
        var error = StrictUtf8.GetString(gate.Error.AsSpan()).Trim();
        return error.Length == 0 ? $" (exit {gate.ExitCode})" : $" (exit {gate.ExitCode}: {error})";
    }

    private static CommandResult Success(int changedFiles) => new(
        true,
        $"C0_RENEWED changed_files={changedFiles} admission=not-evaluated\n",
        string.Empty);
}

internal sealed class ProductionC0RenewEnvironment : IC0RenewEnvironment
{
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
        var snapshot = SnapshotDecoder.Decode(repository.ReadRevision(preimage.Revision)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
        return new C0RenewState(
            @base,
            preimage,
            snapshot,
            repository.WorkingTreeChanges(),
            Read(RepositoryRules.TowerManifestPath),
            Read(C0CeremonyProjection.CertificatePath));
    }

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
            TimeSpan.FromMinutes(30),
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
            TimeSpan.FromMinutes(30),
            64 * 1024 * 1024);
        return new C0RenewGateResult(
            result.ExitCode == 3 ? 0 : result.ExitCode,
            ImmutableArray.CreateRange(result.StandardOutput),
            ImmutableArray.CreateRange(result.StandardError));
    }

    public IDisposable AcquireInstallLock() => C0RenewInstallLock.Acquire(
        root,
        TimeSpan.FromSeconds(30));

    public void Install(C0RenewOutput output)
    {
        var towerPath = Absolute(RepositoryRules.TowerManifestPath);
        var certificatePath = Absolute(C0CeremonyProjection.CertificatePath);
        var previousCertificate = File.ReadAllBytes(certificatePath);
        IngestCommand.ReplaceLedgerAtomically(
            certificatePath,
            output.CertificateBytes.AsSpan());
        try
        {
            IngestCommand.ReplaceLedgerAtomically(towerPath, output.TowerBytes.AsSpan());
        }
        catch (Exception writeFailure) when (writeFailure is not OutOfMemoryException)
        {
            try
            {
                IngestCommand.ReplaceLedgerAtomically(certificatePath, previousCertificate);
            }
            catch (Exception rollbackFailure) when (rollbackFailure is not OutOfMemoryException)
            {
                throw new AggregateException(
                    "C0 TOWER install failed and certificate rollback also failed",
                    writeFailure,
                    rollbackFailure);
            }

            throw;
        }
    }

    private ImmutableArray<byte> Read(string path)
    {
        var absolute = Absolute(path);
        if (!File.Exists(absolute)) throw new FileNotFoundException("C0 output is missing", absolute);
        return ImmutableArray.CreateRange(File.ReadAllBytes(absolute));
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

internal sealed class C0RenewInstallLock : IDisposable
{
    private readonly Mutex mutex;
    private bool ownsMutex;

    private C0RenewInstallLock(Mutex mutex)
    {
        this.mutex = mutex;
        ownsMutex = true;
    }

    internal static C0RenewInstallLock Acquire(string repositoryRoot, TimeSpan timeout)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        if (timeout <= TimeSpan.Zero)
        {
            throw new ArgumentOutOfRangeException(nameof(timeout));
        }

        var identity = SHA256.HashData(
            Encoding.UTF8.GetBytes(Path.GetFullPath(repositoryRoot)));
        var mutex = new Mutex(
            initiallyOwned: false,
            "StrataLint.C0Renew." + Convert.ToHexStringLower(identity));
        try
        {
            bool acquired;
            try
            {
                acquired = mutex.WaitOne(timeout);
            }
            catch (AbandonedMutexException)
            {
                acquired = true;
            }

            if (!acquired)
            {
                throw new TimeoutException("timed out waiting for the C0 renewal install lock");
            }

            return new C0RenewInstallLock(mutex);
        }
        catch
        {
            mutex.Dispose();
            throw;
        }
    }

    public void Dispose()
    {
        if (!ownsMutex) return;
        ownsMutex = false;
        try
        {
            mutex.ReleaseMutex();
        }
        finally
        {
            mutex.Dispose();
        }
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

            var pins = LeanPinSet.TryReadWorktree(candidate, out _);
            if (pins is not null)
            {
                var runner = new ProductionWorktreeProcessRunner();
                var donor = GitWorktreeInventory.SelectDonor(source, pins, runner);
                if (donor.Donor is not null)
                {
                    _ = LeanCacheProvisioner.Provision(donor, candidate, runner);
                }
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
            TimeSpan.FromMinutes(2),
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
