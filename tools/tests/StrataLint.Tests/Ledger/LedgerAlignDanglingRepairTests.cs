using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class LedgerAlignWriterTests
{
    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, false)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, false, true)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public void ReplacementReconcilesRecordedConsumersAndAlternatingTransitiveEdges(
        bool eventIdentities, bool detachTransitiveConsumer, bool scoped)
    {
        var original = BuildCatalog(
            Module("A"), Module("B", imports: ["A"]), Module("C", imports: ["B"]),
            Module("D"), Module("E"), Module("F", imports: ["E"]));
        var current = new[]
        {
            Module("A") with { StatementMaterial = "new prerequisite statement" },
            Module("B"), Module("C", imports: detachTransitiveConsumer ? [] : ["B"]),
            Module("D"), Module("E", imports: ["C"]), Module("F"),
        };
        using var fixture = new AlignFixture(current);
        fixture.InstallAccepted(RecordedConsumerEvents(original, eventIdentities));
        foreach (var module in current)
            fixture.InstallState(module.Name, original.ByPath[RepoPathFor(module.Name)].StatementId);
        var before = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(before, [], out _));
        var unrelated = fixture.EventBytes("D");

        var result = scoped ? fixture.Align("--selector", PathFor("A")) : fixture.Align();

        Assert.True(result.Success, result.Error);
        var after = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(after, [], out _));
        Assert.Equal(6, after.Length);
        Assert.Equal(6, fixture.StateFileCount());
        Assert.Equal(unrelated, fixture.EventBytes("D"));
        var expected = BuildCatalog(current);
        foreach (var name in new[] { "A", "B", "C", "E", "F" })
        {
            var oldEvent = before.Single(item => item.DescriptorPath == RepoPathFor(name));
            var replacement = after.Single(item => item.DescriptorPath == RepoPathFor(name));
            Assert.NotEqual(oldEvent.EventHash, replacement.EventHash);
            Assert.Equal(expected.ByPath[RepoPathFor(name)].StatementId.Value, fixture.StatePin(name));
            Assert.Equal(fixture.StatePin(name), fixture.EventPin(name));
            if (name != "A")
            {
                Assert.Equal(oldEvent.Payload.GetProperty("statement_id").GetString(),
                    replacement.Payload.GetProperty("statement_id").GetString());
                Assert.Equal(oldEvent.Payload.GetProperty("declaration_statement_ids").GetRawText(),
                    replacement.Payload.GetProperty("declaration_statement_ids").GetRawText());
            }
        }
        foreach (var name in new[] { "B", "F" }.Concat(detachTransitiveConsumer ? ["C"] : Array.Empty<string>()))
            Assert.Empty(after.Single(item => item.DescriptorPath == RepoPathFor(name))
                .Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        if (!detachTransitiveConsumer) AssertPrerequisite(after, "C", "B");
        AssertPrerequisite(after, "E", "C");
        var published = fixture.AllPublishedBytes();
        Assert.True(fixture.AlignWithAcceptedWritesDenied().Success);
        Assert.Equal(published, fixture.AllPublishedBytes());
    }

    [Fact]
    public void ScopedReplacementRepinsChangedRecordedConsumer()
    {
        var original = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var current = new[]
        {
            Module("A") with { StatementMaterial = "new prerequisite statement" },
            Module("B") with { StatementMaterial = "new consumer statement" },
        };
        using var fixture = new AlignFixture(current);
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);

        var result = fixture.Align("--selector", PathFor("A"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("changed=2", result.Output, StringComparison.Ordinal);
        var expected = BuildCatalog(current);
        foreach (var name in new[] { "A", "B" })
        {
            Assert.Equal(expected.ByPath[RepoPathFor(name)].StatementId.Value, fixture.StatePin(name));
            Assert.Equal(fixture.StatePin(name), fixture.EventPin(name));
        }
        Assert.True(DagLedgerLoader.TryOrderClosedDag(ReadRepairEvents(fixture.AcceptedFiles()), [], out _));
    }

    [Theory]
    [InlineData("state-conflict")]
    [InlineData("open-consumer")]
    [InlineData("unrelated-dangling")]
    public void RecordedConsumerReplacementRefusesInvalidPublication(string variant)
    {
        var original = BuildCatalog(Module("A"), Module("B", imports: ["A"]), Module("D"));
        using var fixture = new AlignFixture(
            Module("A") with { StatementMaterial = "new prerequisite statement" },
            Module("B", source: variant == "open-consumer" ? "-- TASK D5-T0001\n" + Source("B") : null,
                axioms: variant == "open-consumer" ? ["sorryAx"] : []), Module("D"));
        fixture.InstallAccepted(original.ClosedNodes.Select(material => EventFile(
            "Freeze", FrozenLedgerCanonicalWriter.FreezeElement(FrozenLedgerCanonicalWriter.FreezePayload(
                variant == "unrelated-dangling" && material.RepoPath == RepoPathFor("D")
                    ? material with { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("unresolved unrelated edge"))] }
                    : material)))));
        foreach (var name in new[] { "A", "B", "D" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        if (variant == "state-conflict") fixture.InstallState("B", StatementId.Create(Sha256("conflicting consumer pin")));
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--selector", PathFor("A"));

        Assert.False(result.Success);
        Assert.Contains(variant switch
        {
            "state-conflict" => "conflict",
            "open-consumer" => "TruthState=Open",
            _ => "does not form a closed dependency DAG",
        }, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DanglingRepairReconcilesRecordedConsumerThenCurrentDescendant()
    {
        var original = BuildCatalog(RepairModules());
        using var fixture = new AlignFixture(
            Module("A"), Module("B", imports: ["A"]), Module("C"), Module("D", imports: ["C"]));
        fixture.InstallAccepted(DanglingEvents(original));
        foreach (var name in new[] { "A", "B", "C", "D" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
        var stable = fixture.EventBytes("A");

        var result = fixture.Align("--selector", PathFor("B"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("seed_modules=1 reattested_modules=3", result.Output, StringComparison.Ordinal);
        var after = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(after, [], out _));
        Assert.Equal(stable, fixture.EventBytes("A"));
        AssertPrerequisite(after, "B", "A");
        AssertPrerequisite(after, "D", "C");
        Assert.Empty(after.Single(item => item.DescriptorPath == RepoPathFor("C"))
            .Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        foreach (var name in new[] { "A", "B", "C", "D" })
            Assert.Equal(original.ByPath[RepoPathFor(name)].StatementId.Value, fixture.StatePin(name));
    }

    private static ImmutableArray<RepositoryFile> RecordedConsumerEvents(
        FrozenMaterialCatalog catalog, bool eventIdentities)
    {
        var events = ImmutableArray.CreateBuilder<RepositoryFile>();
        var eventByNode = new Dictionary<FrozenNodeId, FrozenNodeId>();
        foreach (var material in catalog.ClosedNodes.OrderBy(static item => item.RepoPath.Value, StringComparer.Ordinal))
        {
            var recorded = eventIdentities ? material with
            {
                PrerequisiteFrozenNodeIds = material.PrerequisiteFrozenNodeIds
                    .Select(identity => eventByNode[identity]).OrderBy(static identity => identity.Value, StringComparer.Ordinal)
                    .ToImmutableArray(),
            } : material;
            var file = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(recorded)));
            eventByNode.Add(material.FrozenNodeId, FrozenNodeId.Create(Assert.Single(ReadRepairEvents([file])).EventHash));
            events.Add(file);
        }
        return events.ToImmutable();
    }

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
        Assert.Empty(RuleCatalog.Default.EvaluateDeltaSingle(RuleId.CreateKnown(8), context).Diagnostics);
        // No state addition or pin change: this is not a first Freeze requiring utility admission.
        Assert.Empty(RuleCatalog.Default.EvaluateDeltaSingle(RuleId.CreateKnown(31), context).Diagnostics);
    }

    private static void AssertPrerequisite(ImmutableArray<DagLedgerFileEvent> events, string name, string dependency)
    {
        var item = events.Single(item => item.DescriptorPath == RepoPathFor(name));
        var prerequisite = Assert.Single(item.Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        Assert.Equal(events.Single(item => item.DescriptorPath == RepoPathFor(dependency)).EventHash,
            prerequisite.GetString());
    }
}
