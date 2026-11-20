using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class PullRequestLeanScopeTests
{
    [Fact]
    public void DeletedScribeSourceRejectsItsOrphanMarkdownBeforeLeanSelection()
    {
        using var temporary = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(temporary.Resolve("global.json"), "{}");
        TemporaryFileSystem.File.WriteAllText(temporary.Resolve("Blueprint/D5/Missing.md"), "# Orphan");
        using var error = new StringWriter();
        var code = ScribeCli.Run(["lean-inputs", "--affected", "--paths-from", "-"], temporary.Path,
            TextWriter.Null, error, new StringReader("Blueprint/D5/Missing.scribe.cs\0"));
        Assert.Equal(2, code);
        Assert.Contains("no matching .scribe.cs source", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ScopedProofCheckRejectsUnfrozenSorryAndPreservesFrontierException()
    {
        var incomplete = new LeanFileReport([], [new LeanDeclaration("probe", "theorem", "True", ["sorryAx"])]);
        var report = LeanAxiomReport.CreateScoped(new Dictionary<string, LeanFileReport>
        {
            ["D5/Incomplete.lean"] = incomplete, ["D5/X_Frontier/Allowed.lean"] = incomplete,
        });
        var finding = Assert.Single(PullRequestLeanChecks.ProofFindings(report));
        Assert.Equal("D5/Incomplete.lean", finding.Path);
        Assert.Contains("sorryAx", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeletedModuleReachesSurvivingImportersAndAuditorWithoutSelectingUnrelatedModules()
    {
        var sources = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText("D5/Middle.lean", "public meta import all D5.Removed\n"),
            RawRepositoryEntry.FromText("Reg/Top.lean", "/- ignored import D5.Other -/\nimport D5.Middle\n"),
            RawRepositoryEntry.FromText("tools/lean-inspector/LeanInformationAuditRegTests/Probe.lean", "import Reg.Top\n"),
            RawRepositoryEntry.FromText("D5/Other.lean", "def other := 1\n"),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(sources)).Snapshot;
        var targets = new HashSet<string>(StringComparer.Ordinal);
        var programs = new HashSet<string>(StringComparer.Ordinal);
        PullRequestLeanChecks.AddAffectedModules(snapshot, ["D5.Removed"], targets, programs);
        Assert.Equal(["D5.Middle", "Reg.Top"], targets.Order(StringComparer.Ordinal));
        Assert.Equal("LeanInformationAuditRegTests.Probe", Assert.Single(programs));
    }
}
