using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class DagLedgerMathlibReanchorWriterTests
{
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
    public void CompletedUpstreamRetirementRequiresExplicitSelectorsAndPreservedDescendants(
        string variant, bool accepted)
    {
        var originalModules = new[]
        {
            ModuleWithReport("A", ModuleASource, "True"),
            ModuleWithReport("B", ModuleBSource, "True") with { Imports = ["A"] },
            ModuleWithReport("C", "theorem c : True := by trivial\n", "True"),
        };
        var currentB = ModuleWithReport("B",
            variant == "weakened-descendant" ? "theorem b : True ∧ True := by constructor <;> trivial\n" : ModuleBSource,
            variant == "weakened-descendant" ? "True and True" : "compiler-reanchored B") with
        {
            Imports = variant == "remaining-import" ? ["A"] : [],
        };
        var currentModules = new[] { currentB }.Concat(
            variant == "unrequested-retirement" ? [] : new[] { originalModules[2] }).Concat(
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
