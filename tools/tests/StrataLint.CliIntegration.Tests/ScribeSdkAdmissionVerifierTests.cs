using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.TestSupport;

namespace StrataLint.CliIntegration.Tests;

public sealed class ScribeSdkAdmissionVerifierTests
{
    [Fact]
    public void MaterializedCandidateReportsSdkDiagnosticBeforeExecutingDefinitions()
    {
        var files = Inputs();
        files[Entry] = Definition("private static int Unused() => 1;");
        var error = Assert.Throws<ScribeSdkAdmissionException>(() => new ProductionScribeEmissionVerifier().Verify(
            Snapshot(files), EmptyReport(), RawChangeSet.Create([Entry])));
        Assert.Contains("ScribeSdkDiagnostic", error.Message, StringComparison.Ordinal);
        Assert.Contains("IDE0051", error.Message, StringComparison.Ordinal);
        Assert.Contains(Entry, error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("CreateFailed", error.Message, StringComparison.Ordinal);
        Assert.Equal(1, error.ExitCode);
    }

    [Fact]
    public void MaterializedCandidateRequiresItsOwnSdkConfiguration()
    {
        var files = Inputs();
        files[Entry] = Definition("");
        files.Remove(".editorconfig");
        var error = Assert.Throws<ScribeSdkAdmissionException>(() => new ProductionScribeEmissionVerifier().Verify(
            Snapshot(files), EmptyReport(), RawChangeSet.Create([Entry])));
        Assert.Contains("ScribeSdkInfrastructure", error.Message, StringComparison.Ordinal);
        Assert.Contains(".editorconfig", error.Message, StringComparison.Ordinal);
        Assert.Equal(2, error.ExitCode);
    }

    private const string Entry = "Blueprint/D5/S0/Test/Probe.scribe.cs";
    private static LeanAxiomReport EmptyReport() => LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
    private static Dictionary<string, string> Inputs()
    {
        var files = new RuleFixture().Files.ToDictionary(StringComparer.Ordinal);
        foreach (var (path, text) in ScribeSdkFixtureInputs.Read()) files[path] = text;
        files["Meta/ReportProducers/scribe-content.json"] = """
            {"schema":"report-producer-scope-v2","registration":"lean-report-inputs.json",
             "scope":"scribe-content","projects":[]}
            """;
        files["lean-report-inputs.json"] = """
            {"inspector_sources":{"include":[],"exclude":[]},"producer_scopes":{
             "lean-report":{"include":[],"exclude":[]},"scribe-content":{"include":[],"exclude":[]}}}
            """;
        return files;
    }

    private static RepositorySnapshot Snapshot(Dictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Key, file.Value))))).Snapshot;

    private static string Definition(string member) => $$"""
        using StrataLint.Scribe;
        internal sealed class Probe : IScribeDocumentDefinition
        {
            {{member}}
            public DocumentDefinition Create() => null!;
        }
        """;
}
