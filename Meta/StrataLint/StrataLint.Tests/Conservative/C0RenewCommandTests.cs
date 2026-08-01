using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class C0RenewCommandTests
{
    private static readonly string BaseCommit = new('a', 40);
    private static readonly string BaseTree = new('b', 40);
    private static readonly string PreimageCommit = new('c', 40);
    private static readonly string PreimageTree = new('d', 40);

    private static string[] Arguments(string? baseCommit = null) =>
    [
        "--base",
        baseCommit ?? BaseCommit,
        "--deadline-seconds",
        "16200",
    ];

    [Fact]
    public void CeremonyBudgetsMatchColdScratchCalibration()
    {
        Assert.True(
            ProductionC0RenewEnvironment.LeanReportBudgetMinutes
            > ProductionConservativeExtensionEnvironment.DefaultEvaluationBudgetSeconds / 60);
        Assert.True(
            ProductionC0RenewEnvironment.LeanReportBudgetMinutes
            > ProductionC0RenewEnvironment.GitOperationBudgetMinutes);
    }

    [Fact]
    public void CeremonyDeadlineCapsChildrenAndFailsClosedWhenExhausted()
    {
        var elapsed = TimeSpan.Zero;
        var deadline = new C0RenewDeadline(
            TimeSpan.FromSeconds(20),
            () => elapsed);

        Assert.Equal(TimeSpan.FromSeconds(10), deadline.Remaining(TimeSpan.FromSeconds(10)));
        elapsed = TimeSpan.FromSeconds(15);
        Assert.Equal(TimeSpan.FromSeconds(5), deadline.Remaining(TimeSpan.FromSeconds(10)));
        elapsed = TimeSpan.FromSeconds(20);
        Assert.Throws<TimeoutException>(() => deadline.Remaining(TimeSpan.FromSeconds(10)));
    }

    [Fact]
    public void MutableBaseReferenceIsRejectedBeforeRepositoryAccess()
    {
        var environment = new SyntheticRenewEnvironment(Certificate());

        var result = C0RenewCommand.Run(Arguments("origin/dev"), environment);

        Assert.False(result.Success);
        Assert.Contains("exact 40-character lowercase commit", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, environment.StateReads);
    }

    [Fact]
    public void NestedGateFailureEmitsOuterAndInnerExceptionFingerprints()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(),
            gateException: new InvalidOperationException(
                "outer gate failure",
                new IOException("inner gate failure")));

        var result = C0RenewCommand.Run(Arguments(), environment);

        Assert.False(result.Success);
        Assert.Contains(
            "C0_RENEW_FAILED [InvalidOperationException] outer gate failure",
            result.Error,
            StringComparison.Ordinal);
        Assert.Contains(
            "C0_RENEW_FAILED_INNER [IOException] inner gate failure",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RepeatedRenewIsAByteExactNoOpAfterGateRevalidation()
    {
        var environment = new SyntheticRenewEnvironment(Certificate());

        var first = C0RenewCommand.Run(Arguments(), environment);
        var firstTower = environment.CurrentTower;
        var firstCertificate = environment.CurrentCertificate;
        var second = C0RenewCommand.Run(Arguments(), environment);

        Assert.True(first.Success, first.Error);
        Assert.Contains("changed_files=2", first.Output, StringComparison.Ordinal);
        Assert.True(second.Success, second.Error);
        Assert.Contains("changed_files=0", second.Output, StringComparison.Ordinal);
        Assert.Equal(2, environment.GateRuns);
        Assert.Equal(2, environment.LockAcquisitions);
        Assert.Equal(1, environment.Installations);
        Assert.Equal(firstTower, environment.CurrentTower);
        Assert.Equal(firstCertificate, environment.CurrentCertificate);
    }

    [Fact]
    public void TamperedCandidateCannotBeLaunderedByRenewAndPostGateRemainsRed()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(status: "CONSERVATIVE_VIOLATION", findings: [new { code = "fixture" }]),
            gateExitCode: 1);
        var beforeTower = environment.CurrentTower;
        var beforeCertificate = environment.CurrentCertificate;

        var renew = C0RenewCommand.Run(Arguments(), environment);
        var postGate = environment.RunConservativeGate(
            BaseCommit,
            PreimageCommit,
            C0RenewDeadline.Start(TimeSpan.FromMinutes(5)));

        Assert.False(renew.Success);
        Assert.Contains("did not produce a renewable certificate", renew.Error, StringComparison.Ordinal);
        Assert.Equal(0, environment.Installations);
        Assert.Equal(beforeTower, environment.CurrentTower);
        Assert.Equal(beforeCertificate, environment.CurrentCertificate);
        Assert.Equal(1, postGate.ExitCode);
    }

    [Fact]
    public void ForgedDirtyOutputsCannotBypassARedGate()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(status: "CONSERVATIVE_VIOLATION", findings: [new { code = "fixture" }]),
            gateExitCode: 1);
        environment.SetDirtyOutputs(Certificate(actualCandidateCaseId: "actual:forged"));
        var beforeTower = environment.CurrentTower;
        var beforeCertificate = environment.CurrentCertificate;

        var renew = C0RenewCommand.Run(Arguments(), environment);

        Assert.False(renew.Success);
        Assert.Contains("did not produce a renewable certificate", renew.Error, StringComparison.Ordinal);
        Assert.Equal(1, environment.GateRuns);
        Assert.Equal(0, environment.Installations);
        Assert.Equal(beforeTower, environment.CurrentTower);
        Assert.Equal(beforeCertificate, environment.CurrentCertificate);
    }

    [Fact]
    public void CandidateFailureRemainsRejectedWhenTheBaseNoOpPasses()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(),
            candidateGateExitCodes: [1],
            noOpGateExitCode: 0);

        var result = C0RenewCommand.Run(Arguments(), environment);

        Assert.False(result.Success);
        Assert.Equal(1, environment.GateRuns);
        Assert.Equal(1, environment.NoOpGateRuns);
        Assert.Equal(0, environment.Installations);
    }

    [Fact]
    public void FailedBaseNoOpPermitsOneOrdinaryGateReplay()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(),
            candidateGateExitCodes: [2, 0],
            noOpGateExitCode: 2);

        var result = C0RenewCommand.Run(Arguments(), environment);

        Assert.True(result.Success, result.Error);
        Assert.Equal(2, environment.GateRuns);
        Assert.Equal(1, environment.NoOpGateRuns);
        Assert.Equal(1, environment.Installations);
    }

    [Fact]
    public void FailedRecoveryReplayRemainsRejected()
    {
        var environment = new SyntheticRenewEnvironment(
            Certificate(),
            candidateGateExitCodes: [2, 1],
            noOpGateExitCode: 2);

        var result = C0RenewCommand.Run(Arguments(), environment);

        Assert.False(result.Success);
        Assert.Contains("ordinary conservative gate replay failed", result.Error, StringComparison.Ordinal);
        Assert.Equal(2, environment.GateRuns);
        Assert.Equal(1, environment.NoOpGateRuns);
        Assert.Equal(0, environment.Installations);
    }

    [Fact]
    public void GateCandidateWorkspaceMaterializesTheCleanCommittedPreimageWithoutDonorCache()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        Write(repository.Path, RepositoryRules.TowerManifestPath, "committed tower\n");
        Write(repository.Path, C0CeremonyProjection.CertificatePath, "committed certificate\n");
        Write(repository.Path, "lean-toolchain", "leanprover/lean4:v4.24.0\n");
        Write(repository.Path, "lake-manifest.json", "{}\n");
        Write(repository.Path, ".gitignore", "/.lake/\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "preimage");
        var preimage = ReviewRegressionTests.RunGit(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();
        Write(repository.Path, ".lake/build/cache-marker", "private cache\n");
        Write(repository.Path, RepositoryRules.TowerManifestPath, "dirty tower\n");
        Write(repository.Path, C0CeremonyProjection.CertificatePath, "dirty certificate\n");

        using var candidate = C0RenewCandidateWorkspace.Materialize(
            repository.Path,
            preimage,
            C0RenewDeadline.Start(TimeSpan.FromMinutes(5)));

        Assert.Equal(
            preimage,
            ReviewRegressionTests.RunGit(candidate.Root, "rev-parse", "HEAD").Trim());
        Assert.Equal(
            string.Empty,
            ReviewRegressionTests.RunGit(
                candidate.Root,
                "status",
                "--porcelain",
                "--untracked-files=all"));
        Assert.Equal(
            "committed tower\n",
            File.ReadAllText(Path.Combine(candidate.Root, RepositoryRules.TowerManifestPath)));
        Assert.Equal(
            "committed certificate\n",
            File.ReadAllText(Path.Combine(candidate.Root, C0CeremonyProjection.CertificatePath)));
        Assert.False(Directory.Exists(Path.Combine(candidate.Root, ".lake")));
    }

    [Fact]
    public void ProductionRenewRunsReportAndGateProgramsFromTheExactBaseInCiMode()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        var localGate = Path.Combine("Meta", "StrataLint", "scripts", "local-harness-gate.sh");
        var reportPair = Path.Combine("Meta", "StrataLint", "scripts", "lean-report-pair.sh");
        Write(repository.Path, localGate, "#!/usr/bin/env bash\nprintf 'BASE_LOCAL\\n'\nexit 2\n");
        Write(repository.Path, reportPair, """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "${STRATALINT_LOCK_TIMEOUT_SECONDS:-}" =~ ^[1-9][0-9]*$ ]]
            [[ "$STRATALINT_LOCK_TIMEOUT_SECONDS" == "$STRATALINT_BUILD_TIMEOUT_SECONDS" ]]
            candidate=''
            baseline=''
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --candidate-output) candidate="$2" ;;
                --baseline-output) baseline="$2" ;;
              esac
              shift 2
            done
            mkdir -p "$(dirname "$candidate")" "$(dirname "$baseline")"
            printf '{}\n' > "$candidate"
            printf '{}\n' > "$baseline"
            """ + "\n");
        Write(
            repository.Path,
            C0CeremonyProjection.GateWiringPath,
            "#!/usr/bin/env bash\n"
            + "[[ \"${CI:-}\" == \"true\" ]] || { printf 'CI_MISSING\\n' >&2; exit 2; }\n"
            + "printf 'BASE_GATE\\n'\n"
            + "exit 3\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "base gate");
        var @base = ReviewRegressionTests.RunGit(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();

        Write(repository.Path, localGate, "#!/usr/bin/env bash\nprintf 'FORGED_LOCAL\\n'\nexit 0\n");
        Write(repository.Path, reportPair, "#!/usr/bin/env bash\nprintf 'FORGED_PAIR\\n'\nexit 0\n");
        Write(
            repository.Path,
            C0CeremonyProjection.GateWiringPath,
            "#!/usr/bin/env bash\nprintf 'FORGED_SHARED\\n'\nexit 0\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "candidate forgery");
        var candidate = ReviewRegressionTests.RunGit(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();

        var result = new ProductionC0RenewEnvironment(repository.Path)
            .RunConservativeGate(
                @base,
                candidate,
                C0RenewDeadline.Start(TimeSpan.FromMinutes(5)));

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("BASE_GATE\n", Encoding.UTF8.GetString(result.Output.AsSpan()));
        Assert.DoesNotContain("FORGED", Encoding.UTF8.GetString(result.Output.AsSpan()));
    }

    [Fact]
    public void ProductionNoOpProbeUsesAnEmptyDescendantAndExactBasePrograms()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        Write(repository.Path, ".gitignore", "/.lake/\n");
        Write(
            repository.Path,
            C0CeremonyProjection.LeanReportPairPath,
            """
            #!/usr/bin/env bash
            set -euo pipefail
            candidate=''
            baseline=''
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --candidate-output) candidate="$2" ;;
                --baseline-output) baseline="$2" ;;
              esac
              shift 2
            done
            mkdir -p "$(dirname "$candidate")" "$(dirname "$baseline")"
            printf '{}\n' > "$candidate"
            printf '{}\n' > "$baseline"
            """ + "\n");
        Write(
            repository.Path,
            C0CeremonyProjection.GateWiringPath,
            """
            #!/usr/bin/env bash
            set -euo pipefail
            candidate=''
            judge=''
            base=''
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --candidate) candidate="$2" ;;
                --judge-root) judge="$2" ;;
                --base) base="$2" ;;
              esac
              shift 2
            done
            [[ "$(git -C "$candidate" rev-parse HEAD^)" == "$base" ]]
            [[ "$(git -C "$candidate" rev-parse HEAD^{tree})" == "$(git -C "$judge" rev-parse HEAD^{tree})" ]]
            [[ -z "$(git -C "$candidate" status --porcelain --untracked-files=all)" ]]
            printf 'BASE_NOOP\n'
            """ + "\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "base gate");
        var @base = ReviewRegressionTests.RunGit(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();

        var result = new ProductionC0RenewEnvironment(repository.Path)
            .RunBaseNoOpGate(
                @base,
                C0RenewDeadline.Start(TimeSpan.FromMinutes(5)));

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("BASE_NOOP\n", Encoding.UTF8.GetString(result.Output.AsSpan()));
    }

    [Fact]
    public void InstallLockSerializesRenewalsForTheSameRepository()
    {
        using var repository = new TemporaryDirectory();
        using var acquired = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        Exception? ownerFailure = null;
        var owner = new Thread(() =>
        {
            try
            {
                using var held = C0RenewInstallLock.Acquire(
                    repository.Path,
                    TimeSpan.FromSeconds(5));
                acquired.Set();
                release.Wait();
            }
            catch (Exception exception)
            {
                ownerFailure = exception;
                acquired.Set();
            }
        });
        owner.Start();
        Assert.True(acquired.Wait(TimeSpan.FromSeconds(5)), "owner did not acquire the install lock");
        try
        {
            Assert.Null(ownerFailure);
            Assert.Throws<TimeoutException>(() => C0RenewInstallLock.Acquire(
                repository.Path,
                TimeSpan.FromMilliseconds(100)));
        }
        finally
        {
            release.Set();
            Assert.True(owner.Join(TimeSpan.FromSeconds(5)), "lock owner did not exit");
        }

        Assert.Null(ownerFailure);
        using var reacquired = C0RenewInstallLock.Acquire(
            repository.Path,
            TimeSpan.FromSeconds(5));
    }

    private static ImmutableArray<byte> Certificate(
        string status = "CORPUS_CONSERVATIVE",
        object[]? findings = null,
        string actualCandidateCaseId = "actual:candidate-tree")
    {
        findings ??= [];
        var material = JsonSerializer.SerializeToElement(new
        {
            actual_candidate_case = new
            {
                baseline = new { blocking_rules = Array.Empty<string>(), disposition = "admit" },
                candidate = new { blocking_rules = Array.Empty<string>(), disposition = "admit" },
                case_id = actualCandidateCaseId,
            },
            actual_tree_case = new
            {
                baseline = new { blocking_rules = Array.Empty<string>(), disposition = "admit" },
                candidate = new { blocking_rules = Array.Empty<string>(), disposition = "admit" },
                case_id = "actual:baseline-tree",
            },
            baseline = new
            {
                commit_oid = BaseCommit,
                tree_oid = "git-sha1:" + BaseTree,
            },
            candidate = new
            {
                commit_oid = PreimageCommit,
                tree_oid = "git-sha1:" + PreimageTree,
            },
            findings,
            positive_implication = new
            {
                baseline_admit_count = 1,
                preserved_admit_count = 1,
            },
            schema = "stratalint-conservative-certificate-v1",
            status,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static void Write(string root, string path, string contents)
    {
        var absolute = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(absolute)!);
        File.WriteAllText(absolute, contents, new UTF8Encoding(false));
    }

    private static ImmutableArray<byte> TowerBytes() => ImmutableArray.CreateRange(
        Encoding.UTF8.GetBytes("""
            schema_version: 1
            components:
              - id: conservative-extension-gate-c
                kind: phased-gate
                members:
                  - phase1-protected-content-admission
                  - phase2-dual-harness-conservative-extension
                  - "c0/base-commit git-commit/1111111111111111111111111111111111111111"
                  - "c0/ceremony-commit convention/this-pr-merge-commit"
                  - "c0/controller git-sha1/2222222222222222222222222222222222222222 old.cs"
                  - "c0/corpus git-sha1/3333333333333333333333333333333333333333 old.toml"
                  - "c0/gate-wiring git-sha1/4444444444444444444444444444444444444444 gate.sh"
                  - "c0/inaugural-certificate sha256/5555555555555555555555555555555555555555555555555555555555555555 old.json"
                  - "c0/preimage-commit git-commit/6666666666666666666666666666666666666666"
                  - "c0/preimage-tree git-tree/7777777777777777777777777777777777777777"
                judged_by:
                  - bootstrap-pr-1
                verification: verified
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: "Godel boundary."
              genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
              commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """ + "\n"));

    private sealed class SyntheticRenewEnvironment : IC0RenewEnvironment
    {
        private readonly ImmutableArray<byte> gateCertificate;
        private readonly ImmutableArray<int> candidateGateExitCodes;
        private readonly int noOpGateExitCode;
        private readonly Exception? gateException;
        private readonly RepositorySnapshot preimageSnapshot;
        private bool outputsDirty;

        internal SyntheticRenewEnvironment(
            ImmutableArray<byte> gateCertificate,
            int gateExitCode = 0,
            Exception? gateException = null,
            int[]? candidateGateExitCodes = null,
            int noOpGateExitCode = 0)
        {
            this.gateCertificate = gateCertificate;
            this.candidateGateExitCodes = ImmutableArray.CreateRange(
                candidateGateExitCodes ?? [gateExitCode]);
            this.noOpGateExitCode = noOpGateExitCode;
            this.gateException = gateException;
            CurrentTower = TowerBytes();
            CurrentCertificate = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{}\n"));
            preimageSnapshot = Snapshot(CurrentTower, CurrentCertificate);
        }

        internal int GateRuns { get; private set; }

        internal int NoOpGateRuns { get; private set; }

        internal int StateReads { get; private set; }

        internal int Installations { get; private set; }

        internal int LockAcquisitions { get; private set; }

        internal ImmutableArray<byte> CurrentTower { get; private set; }

        internal ImmutableArray<byte> CurrentCertificate { get; private set; }

        public C0RenewState ReadState(string baseReference)
        {
            StateReads++;
            Assert.Equal(BaseCommit, baseReference);
            var changed = outputsDirty
                ? [RepositoryRules.TowerManifestPath, C0CeremonyProjection.CertificatePath]
                : ImmutableArray<string>.Empty;
            return new C0RenewState(
                new FrozenRevisionIdentity(BaseCommit, "git-sha1:" + BaseCommit, "git-sha1:" + BaseTree),
                new FrozenRevisionIdentity(
                    PreimageCommit,
                    "git-sha1:" + PreimageCommit,
                    "git-sha1:" + PreimageTree),
                preimageSnapshot,
                changed,
                CurrentTower,
                CurrentCertificate);
        }

        public C0RenewGateResult RunConservativeGate(
            string exactBaseCommit,
            string exactPreimageCommit,
            C0RenewDeadline deadline)
        {
            Assert.Equal(BaseCommit, exactBaseCommit);
            Assert.Equal(PreimageCommit, exactPreimageCommit);
            GateRuns++;
            if (gateException is not null && GateRuns == 1) throw gateException;
            var prefix = Encoding.UTF8.GetBytes("PROTECTED_SURFACE_CHANGE fixture\n");
            var suffix = Encoding.UTF8.GetBytes("gate summary\n");
            return new C0RenewGateResult(
                candidateGateExitCodes[Math.Min(GateRuns - 1, candidateGateExitCodes.Length - 1)],
                ImmutableArray.CreateRange(prefix.Concat(gateCertificate).Concat(suffix)),
                ImmutableArray<byte>.Empty);
        }

        public C0RenewGateResult RunBaseNoOpGate(
            string exactBaseCommit,
            C0RenewDeadline deadline)
        {
            Assert.Equal(BaseCommit, exactBaseCommit);
            NoOpGateRuns++;
            return new C0RenewGateResult(
                noOpGateExitCode,
                ImmutableArray<byte>.Empty,
                ImmutableArray<byte>.Empty);
        }

        public void Install(C0RenewOutput output)
        {
            Installations++;
            CurrentTower = output.TowerBytes;
            CurrentCertificate = output.CertificateBytes;
            outputsDirty = true;
        }

        public IDisposable AcquireInstallLock()
        {
            LockAcquisitions++;
            return new ActionOnDispose(static () => { });
        }

        internal void SetDirtyOutputs(ImmutableArray<byte> certificate)
        {
            var members = C0CeremonyProjection.CreateMembers(
                preimageSnapshot,
                certificate.AsSpan(),
                new C0CeremonyIdentity(BaseCommit, PreimageCommit, PreimageTree));
            CurrentTower = C0TowerProjection.Write(TowerBytes().AsSpan(), members);
            CurrentCertificate = certificate;
            outputsDirty = true;
        }

        private static RepositorySnapshot Snapshot(
            ImmutableArray<byte> tower,
            ImmutableArray<byte> certificate)
        {
            var files = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal)
            {
                [RepositoryRules.TowerManifestPath] = tower,
                [C0CeremonyProjection.CertificatePath] = certificate,
                [C0CeremonyProjection.CliApplicationPath] = Bytes("// cli\n"),
                [C0CeremonyProjection.ProductionEnvironmentPath] =
                    Bytes("// environment\n"),
                [C0CeremonyProjection.GitRepositoryGatewaySourcePath] =
                    Bytes("// git gateway\n"),
                [C0CeremonyProjection.GitRepositoryGatewayFrozenLedgerSourcePath] =
                    Bytes("// frozen git gateway\n"),
                [C0CeremonyProjection.FrozenEvidenceResolverSourcePath] =
                    Bytes("// frozen evidence resolver\n"),
                [C0CeremonyProjection.ProgramPath] = Bytes("// program\n"),
                ["Meta/StrataLint/StrataLint.Cli/Conservative/Worker.cs"] =
                    Bytes("// controller\n"),
                [C0CeremonyProjection.ProjectionSourcePath] =
                    Bytes("// projection\n"),
                [C0CeremonyProjection.ActualValidatorPath] =
                    Bytes("// validator\n"),
                [C0CeremonyProjection.TowerManifestSourcePath] =
                    Bytes("// manifest\n"),
                [C0CeremonyProjection.TowerParserSourcePath] =
                    Bytes("// parser\n"),
                ["Meta/StrataLint/StrataLint.Cli/Golden/Corpus.cs"] = Bytes("// corpus\n"),
                ["Golden/cases/case.toml"] = Bytes("[[cases]]\n"),
                [C0CeremonyProjection.FixtureRegistryPath] = Bytes("schema_version: 1\n"),
                [C0CeremonyProjection.ValuesKernelDataPath] = Bytes("schema_version = 1\n"),
                [C0CeremonyProjection.GateWiringPath] = Bytes("#!/bin/bash\n"),
                [C0CeremonyProjection.LocalGateWiringPath] = Bytes("#!/bin/bash\n"),
                [C0CeremonyProjection.LeanReportPairPath] = Bytes("#!/bin/bash\n"),
                [C0CeremonyProjection.LeanInspectorScriptPath] = Bytes("#!/bin/bash\n"),
                [C0CeremonyProjection.LeanInspectorSourcePath] =
                    Bytes("def main := pure ()\n"),
            };
            var raw = RawRepositorySnapshot.Create(files.Select(static item =>
                new RawRepositoryEntry(item.Key, item.Value)));
            return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        }

        private static ImmutableArray<byte> Bytes(string value) =>
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(value));
    }

    private sealed class ActionOnDispose(Action action) : IDisposable
    {
        public void Dispose() => action();
    }
}
