using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class C0RenewCommandTests
{
    private static readonly string BaseCommit = new('a', 40);
    private static readonly string PreimageCommit = new('c', 40);

    [Fact]
    public void CeremonyBudgetsMatchColdScratchCalibration()
    {
        Assert.Equal(90, ProductionC0RenewEnvironment.LeanReportBudgetMinutes);
        Assert.Equal(10, ProductionC0RenewEnvironment.GitOperationBudgetMinutes);
        Assert.Equal(600, ProductionConservativeExtensionEnvironment.DefaultEvaluationBudgetSeconds);
    }

    [Fact]
    public void CleanPreimageRunsLiveGateWithoutRewritingFrozenRoots()
    {
        var environment = new SyntheticRenewEnvironment();

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.True(result.Success, result.Error);
        Assert.Equal("C0_VERIFIED changed_files=0 admission=not-evaluated\n", result.Output);
        Assert.Equal(1, environment.GateRuns);
    }

    [Fact]
    public void RedGateRemainsRed()
    {
        var environment = new SyntheticRenewEnvironment(gateExitCode: 1);

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.False(result.Success);
        Assert.Contains("did not produce a renewable certificate", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RedGateReportsRuleRejectedOutputVerbatimAlongsideError()
    {
        const string ruleRejected = "RULE_REJECTED SL-001 first violation\n"
            + "RULE_REJECTED SL-022 second violation\n";
        const string gateError = "unrelated gate summary\n";
        var environment = new SyntheticRenewEnvironment(
            gateExitCode: 1,
            gateOutput: ruleRejected,
            gateError: gateError);

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.False(result.Success);
        Assert.Contains(ruleRejected, result.Error, StringComparison.Ordinal);
        Assert.Contains(gateError, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DirtyPreimageCannotEnterTheCeremony()
    {
        var environment = new SyntheticRenewEnvironment(changedPaths: ["changed.cs"]);

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.False(result.Success);
        Assert.Contains("requires a clean committed preimage", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, environment.GateRuns);
    }

    [Fact]
    public void MismatchedTrustRootFailsBeforeRunningTheConservativeGate()
    {
        var environment = new SyntheticRenewEnvironment(mismatchedTrustRoot: true);

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.False(result.Success);
        Assert.Contains("expected c0/inaugural-certificate sha256/", result.Error, StringComparison.Ordinal);
        Assert.Contains("actual c0/inaugural-certificate sha256/", result.Error, StringComparison.Ordinal);
        Assert.Contains("expected c0/preimage-tree git-tree/", result.Error, StringComparison.Ordinal);
        Assert.Contains("actual c0/preimage-tree git-tree/", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, environment.GateRuns);
    }

    private sealed class SyntheticRenewEnvironment(
        int gateExitCode = 0,
        ImmutableArray<string> changedPaths = default,
        string gateOutput = "",
        string gateError = "",
        bool mismatchedTrustRoot = false) : IC0RenewEnvironment
    {
        internal int GateRuns { get; private set; }

        public C0RenewState ReadState(string baseReference)
        {
            Assert.Equal(BaseCommit, baseReference);
            return new C0RenewState(
                new FrozenRevisionIdentity(BaseCommit, "git-sha1:" + BaseCommit, "git-sha1:" + new string('b', 40)),
                new FrozenRevisionIdentity(PreimageCommit, "git-sha1:" + PreimageCommit, "git-sha1:" + new string('d', 40)),
                changedPaths.IsDefault ? ImmutableArray<string>.Empty : changedPaths,
                Snapshot(mismatchedTrustRoot));
        }

        public C0RenewGateResult RunConservativeGate(
            string exactBaseCommit,
            string exactPreimageCommit)
        {
            Assert.Equal(BaseCommit, exactBaseCommit);
            Assert.Equal(PreimageCommit, exactPreimageCommit);
            GateRuns++;
            return new C0RenewGateResult(
                gateExitCode,
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(gateOutput)),
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(gateError)));
        }

        private static RepositorySnapshot Snapshot(bool mismatched)
        {
            var certificate = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
            {
                candidate = new { tree_oid = "git-sha1:" + new string('a', 40) },
                findings = Array.Empty<object>(),
                positive_implication = new
                {
                    baseline_admit_count = 1,
                    preserved_admit_count = 1,
                },
                schema = "stratalint-conservative-certificate-v1",
                status = "CORPUS_CONSERVATIVE",
            }));
            var expected = C0CeremonyProjection.CreateTrustRootMembers(
                Decode(new Dictionary<string, ImmutableArray<byte>>
                {
                    [C0CeremonyProjection.CertificatePath] = certificate,
                }));
            var members = mismatched
                ? expected.Select(member => member.StartsWith("c0/inaugural-certificate ", StringComparison.Ordinal)
                    ? $"c0/inaugural-certificate sha256/{new string('f', 64)} {C0CeremonyProjection.CertificatePath}"
                    : member.StartsWith("c0/preimage-tree ", StringComparison.Ordinal)
                        ? $"c0/preimage-tree git-tree/{new string('b', 40)}"
                        : member).ToImmutableArray()
                : expected;
            var tower = C0TowerProjection.Write(ProductionTowerBytes().AsSpan(), members);
            return Decode(new Dictionary<string, ImmutableArray<byte>>
            {
                [C0CeremonyProjection.CertificatePath] = certificate,
                [RepositoryRules.TowerManifestPath] = tower,
            });
        }

        private static ImmutableArray<byte> ProductionTowerBytes()
        {
            var directory = new DirectoryInfo(AppContext.BaseDirectory);
            while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "CLAUDE.md")))
            {
                directory = directory.Parent;
            }

            Assert.NotNull(directory);
            return ImmutableArray.CreateRange(File.ReadAllBytes(
                Path.Combine(directory.FullName, RepositoryRules.TowerManifestPath)));
        }

        private static RepositorySnapshot Decode(
            IReadOnlyDictionary<string, ImmutableArray<byte>> files)
        {
            var raw = RawRepositorySnapshot.Create(files.Select(static item =>
                new RawRepositoryEntry(item.Key, item.Value)));
            return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        }
    }
}
