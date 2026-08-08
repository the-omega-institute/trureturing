using System.Collections.Immutable;
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
    public void DirtyPreimageCannotEnterTheCeremony()
    {
        var environment = new SyntheticRenewEnvironment(changedPaths: ["changed.cs"]);

        var result = C0RenewCommand.Run(["--base", BaseCommit], environment);

        Assert.False(result.Success);
        Assert.Contains("requires a clean committed preimage", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, environment.GateRuns);
    }

    private sealed class SyntheticRenewEnvironment(
        int gateExitCode = 0,
        ImmutableArray<string> changedPaths = default) : IC0RenewEnvironment
    {
        internal int GateRuns { get; private set; }

        public C0RenewState ReadState(string baseReference)
        {
            Assert.Equal(BaseCommit, baseReference);
            return new C0RenewState(
                new FrozenRevisionIdentity(BaseCommit, "git-sha1:" + BaseCommit, "git-sha1:" + new string('b', 40)),
                new FrozenRevisionIdentity(PreimageCommit, "git-sha1:" + PreimageCommit, "git-sha1:" + new string('d', 40)),
                changedPaths.IsDefault ? ImmutableArray<string>.Empty : changedPaths);
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
                ImmutableArray<byte>.Empty,
                ImmutableArray<byte>.Empty);
        }
    }
}
