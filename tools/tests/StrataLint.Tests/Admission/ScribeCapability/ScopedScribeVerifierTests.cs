using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Tests;

public sealed class ScopedScribeVerifierTests
{
    [Fact]
    public void MissingScopeFailsBeforeAnyDefinitionRuns()
    {
        var called = false;
        var verifier = new ProductionScribeEmissionVerifier((_, _, _, _) =>
        {
            called = true;
            return VerifiedScribeEmissions.Empty;
        });
        var error = Assert.Throws<InvalidOperationException>(() => verifier.Verify(
            Snapshot(), Report(), (RawChangeSet?)null));
        Assert.Contains("SCRIBE_SCOPE_REQUIRED", error.Message, StringComparison.Ordinal);
        Assert.False(called);
    }

    [Fact]
    public void ScopedVerifierExecutesOnlySelectedDefinitionAndReturnsOnlyItsCapability()
    {
        var verifier = new ProductionScribeEmissionVerifier();
        var snapshot = Snapshot();
        var capability = verifier.Verify(snapshot, Report(), RawChangeSet.Create([Selected]));
        Assert.True(capability.TryGet("D5/S0/Test/Selected", out _));
        Assert.False(capability.TryGet("D5/S0/Test/Unselected", out _));
    }

    [Fact]
    public void EmptyScopeDoesNotExecuteInvalidDefinitions()
    {
        var capability = new ProductionScribeEmissionVerifier().Verify(Snapshot(), Report(), RawChangeSet.Create([]));
        Assert.Equal(VerifiedScribeEmissions.Empty.WriteMaterial(), capability.WriteMaterial());
    }

    [Fact]
    public void BlueprintDefinitionsAreDataOutsideJudgeBuildInputs()
    {
        Assert.False(StrataLintEngineBuildInputs.ContainsJudgeSource(Selected));
        Assert.True(StrataLintEngineBuildInputs.ContainsJudgeSource("tools/StrataLint.Scribe/Scripting/ScribeScriptHost.cs"));
    }

    private const string Selected = "Blueprint/D5/S0/Test/Selected.scribe.cs";
    private static LeanAxiomReport Report() => LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
    private static RepositorySnapshot Snapshot()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/ReportProducers/scribe-content.json"] = """
            {"schema":"report-producer-scope-v2","registration":"lean-report-inputs.json",
             "scope":"scribe-content","projects":[]}
            """;
        fixture.Files["lean-report-inputs.json"] = """
            {"inspector_sources":{"include":[],"exclude":[]},"producer_scopes":{
             "lean-report":{"include":[],"exclude":[]},"scribe-content":{"include":[],"exclude":[]}}}
            """;
        fixture.Files["D5/S0/Test/Selected.lean"] = "-- fixture";
        fixture.Files[Selected] = """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Selected : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Selected"), Blocks(Paragraph(Text("body")))));
            }
            """;
        fixture.Files["Blueprint/D5/S0/Test/Unselected.scribe.cs"] = "invalid C# source";
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            fixture.Files.Select(file => RawRepositoryEntry.FromText(file.Key, file.Value))))).Snapshot;
    }
}
