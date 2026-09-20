using System.Text;
using StrataLint.Engine;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class RegReportMembershipTests
{
    private const string PathName = "Reg/D5/S3/Arith/X.lean";
    private const string Source = "theorem support : True := True.intro\n";

    [Fact]
    public void RegModuleIsRequiredInClosureAndRoundTripsInRawReport()
    {
        var snapshot = Snapshot(PathName);
        Assert.IsType<LeanValidationOutcome.InfrastructureFailure>(LeanClosureValidator.Validate(
            snapshot, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>())));
        var report = Report(PathName, []);
        var raw = RawLeanReportArtifact.Write(snapshot, report);
        Assert.Contains("Reg.D5.S3.Arith.X", Encoding.UTF8.GetString(raw.AsSpan()), StringComparison.Ordinal);
        var read = RawLeanReportArtifact.Read(raw.AsSpan(), snapshot);
        Assert.Equal(PathName, Assert.Single(read.Files).Key.Value);
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(snapshot, read)).Capability;
        Assert.Empty(LeanTruthStates.Resolve(snapshot, closure));
        Assert.False(LeanClosureValidator.IsManagedLean(PathName));
        Assert.False(Gid.TryParse("Reg/D5/S3/Arith/X.support", out _));
    }

    [Theory]
    [InlineData("Reg/D5/S3/Arith/X.lean", "sorryAx", 2)]
    [InlineData("Reg/D5/X_Frontier/X.lean", "sorryAx", 2)]
    [InlineData("Reg/Support/X.lean", "privateAxiom", 20)]
    public void RegProofsRemainSubjectToAxiomChecks(string path, string axiom, int rule)
    {
        var current = Current(Snapshot(path), Report(path, [axiom]));
        Assert.NotEmpty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(rule), current).Diagnostics);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(4)]
    [InlineData(12)]
    public void RegHasNoStratumMirrorOrHeaderDuty(int rule)
    {
        var current = Current(Snapshot(PathName), Report(PathName, []));
        Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(rule), current).Diagnostics);
    }

    private static RepositorySnapshot Snapshot(string path) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, Source)]))).Snapshot;

    private static LeanAxiomReport Report(string path, string[] axioms) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [path] = new(["D5.S3.Arith.X"], [new LeanDeclaration("support", "theorem", "statement-v1(test)", [.. axioms])
                { NameKey = "ns(n0,7:support)" }]),
        });

    private static CurrentRuleContext Current(RepositorySnapshot snapshot, LeanAxiomReport report)
    {
        var root = TestRepositoryLayout.FindRoot();
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml")))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(snapshot, report)).Capability;
        return CurrentRuleContext.Create(snapshot, policy, lean);
    }
}
