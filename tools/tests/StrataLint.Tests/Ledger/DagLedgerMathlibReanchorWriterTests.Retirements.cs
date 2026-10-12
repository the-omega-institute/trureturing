using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class DagLedgerMathlibReanchorWriterTests
{
    [Fact]
    public void MathlibReanchorDiagnosticRetainsImportedDefinitionWhenOwnerBytesMatch()
    {
        var originalModules = new[]
        {
            ModuleWithReport("B", "import D5.S0.Carrier.C\ntheorem b : p = p := by rfl\n",
                "old p equality") with { Imports = ["C"] },
            ModuleWithReport("C", "def p : Nat := 0\n", "old zero", declarations: ["p"], kind: "def"),
        };
        var candidateModules = new[]
        {
            originalModules[0] with { StatementMaterial = "new p equality" },
            originalModules[1] with { Source = "def p : Nat := 1\n", StatementMaterial = "new one" },
        };
        var originalCatalog = BuildCatalog(originalModules);
        var candidateCatalog = BuildCatalog(candidateModules);
        var original = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            Snapshot(BaseToolchain, Manifest('a'), originalModules, EventFiles(originalCatalog), null))).Snapshot;
        var candidate = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            Snapshot(CandidateToolchain, Manifest('b'), candidateModules, EventFiles(candidateCatalog), null))).Snapshot;

        var failures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(
            original, candidate, ImmutableHashSet.Create(RepoPathFor("B")),
            BaseView(originalCatalog), candidateCatalog);

        Assert.Contains(RepoPathFor("B"), failures);
    }

    [Theory]
    [InlineData("aligned", true)]
    [InlineData("state-remains", false)]
    [InlineData("event-remains", false)]
    [InlineData("source-remains", false)]
    [InlineData("unrequested-retirement", false)]
    [InlineData("weakened-descendant", false)]
    [InlineData("dangling-descendant", false)]
    [InlineData("state-conflict", false)]
    [InlineData("same-pin", false)]
    [InlineData("unknown-owner", false)]
    [InlineData("duplicate-selector", false)]
    [InlineData("remaining-import", false)]
    [InlineData("extra-state", false)]
    [InlineData("invalid-event-hash", false)]
    [InlineData("imported-definition-weakened", false)]
    public void CompletedUpstreamRetirementRequiresExplicitSelectorsAndPreservedDescendants(
        string variant, bool accepted)
    {
        var originalModules = new[]
        {
            ModuleWithReport("A", ModuleASource, "True"),
            ModuleWithReport("B", variant == "imported-definition-weakened"
                ? "import D5.S0.Carrier.C\ntheorem b : p := by contradiction\n" : ModuleBSource,
                "True") with { Imports = variant == "imported-definition-weakened" ? ["A", "C"] : ["A"] },
            variant == "imported-definition-weakened"
                ? ModuleWithReport("C", "def p : Prop := False\n", "False", declarations: ["p"], kind: "def")
                : ModuleWithReport("C", "theorem c : True := by trivial\n", "True"),
        };
        var currentB = ModuleWithReport("B",
            variant == "weakened-descendant" ? "theorem b : True ∧ True := by constructor <;> trivial\n"
                : variant == "imported-definition-weakened" ? originalModules[1].Source : ModuleBSource,
            variant == "weakened-descendant" ? "True and True" : "compiler-reanchored B") with
        {
            Imports = variant == "remaining-import" ? ["A"]
                : variant == "imported-definition-weakened" ? ["C"] : [],
        };
        var currentModules = new[] { currentB }.Concat(
            variant == "unrequested-retirement" ? [] : new[] { variant == "imported-definition-weakened"
                ? originalModules[2] with { Source = "def p : Prop := True\n", StatementMaterial = "True" }
                : originalModules[2] }).Concat(
            variant == "source-remains" ? new[] { originalModules[0] } : []).ToArray();
        var originalCatalog = BuildCatalogWithEnvironment(BaseToolchain,
            "[package]\nname = \"fixture\"\n", Manifest('a'), GitOid('c'), GitOid('d'), originalModules);
        // A remaining import is rejected by the report closure before retirement validation.
        var materialModules = currentModules.Select(module => module with { Imports = [] }).ToArray();
        var candidateManifest = Manifest(variant == "same-pin" ? 'a' : 'b');
        var currentCatalog = BuildCatalogWithEnvironment(CandidateToolchain,
            "[package]\nname = \"fixture\"\n", candidateManifest, GitOid('e'), GitOid('f'), materialModules);
        var originalEvents = EventFiles(originalCatalog);
        var currentEvents = EventFiles(currentCatalog);
        if (variant == "event-remains") currentEvents = currentEvents.Add(EventFor(originalEvents, "A"));
        if (variant == "dangling-descendant")
            currentEvents = currentEvents.Remove(EventFor(currentEvents, "B")).Add(EventFor(originalEvents, "B"));
        if (variant == "invalid-event-hash")
        {
            var eventFile = EventFor(currentEvents, "B");
            var eventHash = LoadEvents([eventFile]).Single().EventHash;
            var text = eventFile.Text.Replace(eventHash, "sha256:" + new string('f', 64), StringComparison.Ordinal);
            currentEvents = currentEvents.Remove(eventFile).Add(new RepositoryFile(eventFile.Path,
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)), text));
        }
        var baseline = Snapshot(BaseToolchain, Manifest('a'), originalModules, originalEvents, null);
        var current = Snapshot(CandidateToolchain, candidateManifest, currentModules, currentEvents, null);
        var stateEntries = materialModules.Select(module => new RawRepositoryEntry(
            FrozenStatePath.FromModulePath(RepoPathFor(module.Name)).Value,
            FrozenStateRecord.Encode(variant == "state-conflict" && module.Name == "B"
                ? originalCatalog.ByPath[RepoPathFor("B")].StatementId
                : currentCatalog.ByPath[RepoPathFor(module.Name)].StatementId))).ToList();
        if (variant == "state-remains") stateEntries.Add(new RawRepositoryEntry(
            FrozenStatePath.FromModulePath(RepoPathFor("A")).Value,
            FrozenStateRecord.Encode(originalCatalog.ByPath[RepoPathFor("A")].StatementId)));
        if (variant == "extra-state") stateEntries.Add(new RawRepositoryEntry(
            FrozenStatePath.FromModulePath(RepoPathFor("Unknown")).Value,
            FrozenStateRecord.Encode(originalCatalog.ByPath[RepoPathFor("A")].StatementId)));
        current = RawRepositorySnapshot.Create(current.Entries.Concat(stateEntries));
        var changes = RawChangeSet.CreateWithKinds([("lean-toolchain", RawChangeKind.Modified),
            ("lake-manifest.json", RawChangeKind.Modified), (PathFor("A"), RawChangeKind.Deleted)]);
        var repository = new FakeRepositoryGateway(changes, current, baseline, changesForBase: _ => changes);
        using var temporary = new TemporaryDirectory();
        var ledgerPath = Path.Combine(temporary.Path, FrozenLedgerChangeClassifier.AcceptedRoot);
        WriteLedgerDirectory(ledgerPath, currentEvents);
        var before = ReadLedgerDirectory(ledgerPath);
        var arguments = new List<string> { "--base", BaseRevision, "--retired-upstream-port",
            PathFor(variant == "unknown-owner" ? "Missing" : "A") };
        if (variant == "duplicate-selector") arguments.AddRange(["--retired-upstream-port", PathFor("A")]);

        var result = DagLedgerMathlibReanchorWriter.Reanchor(temporary.Path, repository,
            new FakeLeanReportSource(Report(currentModules)), arguments);

        Assert.True(accepted == result.Success, result.Error + result.Output);
        Assert.Equal(before, ReadLedgerDirectory(ledgerPath));
        if (accepted)
        {
            Assert.Contains("recognition=completed-canonical-publication retired_upstream_ports=1 retained_descendants=1 published_modules=0",
                result.Output, StringComparison.Ordinal);
            Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);
        }
    }
}
