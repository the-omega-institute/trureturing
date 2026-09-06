using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class LedgerAlignWriterTests
{
    [Theory]
    [InlineData(true, false)]
    [InlineData(false, false)]
    [InlineData(true, true)]
    [InlineData(false, true)]
    public void ResolvedPrerequisiteIdentityDoesNotSeedRepair(bool useFrozenNodeId, bool hasDangling)
    {
        var modules = new[] { Module("A"), Module("B", imports: ["A"]), Module("C", imports: ["A"]) };
        var catalog = BuildCatalog(modules);
        var aFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("A")])));
        var a = Assert.Single(ReadRepairEvents([aFile]));
        Assert.NotEqual(a.EventHash, a.FrozenNodeId.Value);
        var b = catalog.ByPath[RepoPathFor("B")] with
        {
            PrerequisiteFrozenNodeIds = [useFrozenNodeId ? a.FrozenNodeId : FrozenNodeId.Create(a.EventHash)],
        };
        var c = catalog.ByPath[RepoPathFor("C")] with
        {
            PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(hasDangling
                ? Sha256("deleted prerequisite") : a.EventHash)],
        };
        using var fixture = new AlignFixture(modules);
        fixture.InstallAccepted([
            aFile,
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(b))),
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(c))),
        ]);
        foreach (var module in modules)
        {
            fixture.InstallState(module.Name, catalog.ByPath[RepoPathFor(module.Name)].StatementId);
        }
        Assert.Equal(!hasDangling, DagLedgerLoader.TryOrderClosedDag(
            ReadRepairEvents(fixture.AcceptedFiles()), [], out _));
        var healthyBytes = fixture.EventBytes("B");
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align();

        Assert.True(result.Success, result.Error);
        Assert.Contains("changed=0 added=0", result.Output, StringComparison.Ordinal);
        Assert.Equal(healthyBytes, fixture.EventBytes("B"));
        Assert.True(DagLedgerLoader.TryOrderClosedDag(ReadRepairEvents(fixture.AcceptedFiles()), [], out _));
        if (hasDangling)
        {
            Assert.Contains("LEDGER_REPAIR seed_modules=1 reattested_modules=1", result.Output, StringComparison.Ordinal);
            Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);
            AssertPrerequisite(ReadRepairEvents(fixture.AcceptedFiles()), "C", "A");
        }
        else
        {
            Assert.DoesNotContain("LEDGER_REPAIR", result.Output, StringComparison.Ordinal);
            Assert.Equal(before, fixture.AllPublishedBytes());
        }
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void DanglingPrerequisiteRepairReattestsReportDescendantsWithoutChangingStatements(bool useSelector)
    {
        var modules = RepairModules();
        var catalog = BuildCatalog(modules);
        var dangling = DanglingEvents(catalog);
        using var fixture = new AlignFixture(modules);
        fixture.InstallAccepted(dangling);
        foreach (var module in modules)
        {
            fixture.InstallState(module.Name, catalog.ByPath[RepoPathFor(module.Name)].StatementId);
        }

        var before = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.False(DagLedgerLoader.TryOrderClosedDag(before, [], out _));
        var stableA = fixture.EventBytes("A");
        var unrelatedD = fixture.EventBytes("D");

        // Selecting only B must still replace C, whose current import is B.
        var result = useSelector ? fixture.Align("--selector", PathFor("B")) : fixture.Align();

        Assert.True(result.Success, result.Error);
        Assert.Contains("changed=0 added=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("LEDGER_REPAIR seed_modules=1 reattested_modules=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);
        var after = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(after, [], out _));
        Assert.Equal(4, after.Length);
        Assert.Equal(4, fixture.StateFileCount());
        Assert.Equal(stableA, fixture.EventBytes("A"));
        Assert.Equal(unrelatedD, fixture.EventBytes("D"));
        foreach (var name in new[] { "B", "C" })
        {
            var oldEvent = before.Single(item => item.DescriptorPath == RepoPathFor(name));
            var repaired = after.Single(item => item.DescriptorPath == RepoPathFor(name));
            Assert.Equal("Freeze", repaired.EventType);
            Assert.NotEqual(oldEvent.EventHash, repaired.EventHash);
            Assert.Equal(oldEvent.Payload.GetProperty("statement_id").GetString(),
                repaired.Payload.GetProperty("statement_id").GetString());
            Assert.Equal(oldEvent.Payload.GetProperty("declaration_statement_ids").GetRawText(),
                repaired.Payload.GetProperty("declaration_statement_ids").GetRawText());
            Assert.Equal(catalog.ByPath[RepoPathFor(name)].StatementId.Value, fixture.StatePin(name));
        }

        AssertPrerequisite(after, "B", "A");
        AssertPrerequisite(after, "C", "B");
        AssertRepairAdmission(modules, catalog, dangling, fixture.AcceptedFiles());
        var repairedBytes = fixture.AllPublishedBytes();
        var second = fixture.AlignWithAcceptedWritesDenied();
        Assert.True(second.Success, second.Error);
        Assert.Equal(repairedBytes, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DanglingRepairRejectsStillOpenReplacementDagWithoutPublishing()
    {
        var modules = RepairModules();
        var catalog = BuildCatalog(modules);
        var d = catalog.ByPath[RepoPathFor("D")] with
        {
            PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("deleted unrelated prerequisite"))],
        };
        var dangling = DanglingEvents(catalog);
        var dPath = ReadRepairEvents(dangling).Single(item => item.DescriptorPath == d.RepoPath).SourcePath;
        using var fixture = new AlignFixture(modules);
        fixture.InstallAccepted(dangling.Where(file => file.Path != dPath).Append(
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(d)))));
        foreach (var module in modules)
        {
            fixture.InstallState(module.Name, catalog.ByPath[RepoPathFor(module.Name)].StatementId);
        }
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--selector", PathFor("B"));

        Assert.False(result.Success);
        Assert.Contains("does not form a closed dependency DAG", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DanglingRepairRejectsStatementDriftInReportDescendantWithoutPublishing()
    {
        var modules = RepairModules();
        var catalog = BuildCatalog(modules);
        using var fixture = new AlignFixture(modules.Select(module => module.Name == "C"
            ? module with { StatementMaterial = "changed descendant proposition" }
            : module).ToArray());
        fixture.InstallAccepted(DanglingEvents(catalog));
        foreach (var module in modules)
        {
            fixture.InstallState(module.Name, catalog.ByPath[RepoPathFor(module.Name)].StatementId);
        }
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--selector", PathFor("B"));

        Assert.False(result.Success);
        Assert.Contains("AUTHORIZATION overall=fail", result.Error, StringComparison.Ordinal);
        Assert.Contains(PathFor("C"), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DanglingRepairRejectsUnresolvedReportDependencyWithoutPublishing()
    {
        var modules = RepairModules();
        var catalog = BuildCatalog(modules);
        using var fixture = new AlignFixture(modules);
        var events = DanglingEvents(catalog);
        var aPath = ReadRepairEvents(events).Single(item => item.DescriptorPath == RepoPathFor("A")).SourcePath;
        fixture.InstallAccepted(events.Where(file => file.Path != aPath));
        foreach (var name in new[] { "B", "C", "D" })
        {
            fixture.InstallState(name, catalog.ByPath[RepoPathFor(name)].StatementId);
        }
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align();

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    private static ModuleSpec[] RepairModules() =>
    [
        Module("A"), Module("B", imports: ["A"]),
        Module("C", imports: ["B"]), Module("D"),
    ];

    private static ImmutableArray<RepositoryFile> DanglingEvents(FrozenMaterialCatalog catalog)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        var b = catalog.ByPath[RepoPathFor("B")] with
        {
            PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("deleted pre-pin A event"))],
        };
        var bFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(b)));
        var bEvent = Assert.Single(ReadRepairEvents([bFile]));
        foreach (var material in catalog.ClosedNodes)
        {
            if (material.RepoPath == b.RepoPath)
            {
                files.Add(bFile);
                continue;
            }
            var current = material.RepoPath == RepoPathFor("C")
                ? material with { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(bEvent.EventHash)] }
                : material;
            files.Add(EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(current))));
        }
        return files.ToImmutable();
    }

    private static ImmutableArray<DagLedgerFileEvent> ReadRepairEvents(IEnumerable<RepositoryFile> files) =>
        Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(FrozenAcceptedEventLoader.LoadFiles(files)).Events;

    private static void AssertRepairAdmission(
        ModuleSpec[] modules,
        FrozenMaterialCatalog catalog,
        ImmutableArray<RepositoryFile> before,
        ImmutableArray<RepositoryFile> after)
    {
        var fixture = new RuleFixture();
        foreach (var module in modules)
        {
            var path = PathFor(module.Name);
            fixture.Files[path] = module.Source;
            fixture.Baseline[path] = module.Source;
            var statePath = FrozenStatePath.FromModulePath(RepoPathFor(module.Name)).Value;
            var state = $"{{\"statement_id\":\"{catalog.ByPath[RepoPathFor(module.Name)].StatementId.Value}\"}}\n";
            fixture.Files[statePath] = state;
            fixture.Baseline[statePath] = state;
        }
        AddLedgerFiles(fixture.Baseline, before);
        AddLedgerFiles(fixture.Files, after);
        var oldPaths = before.Select(static file => file.Path).ToImmutableHashSet();
        var newPaths = after.Select(static file => file.Path).ToImmutableHashSet();
        var changes = RawChangeSet.CreateWithKinds(oldPaths.Except(newPaths)
            .Select(static path => (path.Value, RawChangeKind.Deleted))
            .Concat(newPaths.Except(oldPaths).Select(static path => (path.Value, RawChangeKind.Added))));
        var context = fixture.BuildForRuleCompatibility(changes);
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(8), context).Diagnostics);
        // No state addition or pin change: this is not a first Freeze requiring utility admission.
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(31), context).Diagnostics);
    }

    private static void AssertPrerequisite(ImmutableArray<DagLedgerFileEvent> events, string name, string dependency)
    {
        var item = events.Single(item => item.DescriptorPath == RepoPathFor(name));
        var prerequisite = Assert.Single(item.Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        Assert.Equal(events.Single(item => item.DescriptorPath == RepoPathFor(dependency)).EventHash,
            prerequisite.GetString());
    }
}
