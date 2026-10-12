using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class LedgerAlignWriterTests
{
    [Fact]
    public void DuplicateRepairUsesCurrentMaterialAndReattestsBothRecordedIdentityBranches()
    {
        var modules = DuplicateRepairModules();
        var catalog = BuildCatalog(modules);
        var duplicates = DuplicateEvents(catalog);
        using var fixture = new AlignFixture(modules);
        using var canonical = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, catalog, duplicates);
        var before = fixture.AllPublishedBytes();
        var stateBefore = fixture.StateBytes();
        var stableA = fixture.EventBytes("A");
        var stableU = fixture.EventBytes("U");

        Assert.Throws<FormatException>(() => FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            duplicates.ToImmutableDictionary(static file => file.Path))));
        var ordinary = fixture.Align("--add", PathFor("B"));
        Assert.False(ordinary.Success);
        Assert.Contains("duplicate descriptor_selector", ordinary.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());

        var result = fixture.Align(DuplicateRepairOptions());
        var canonicalResult = canonical.Align(modules.SelectMany(module => new[] { "--add", PathFor(module.Name) }).ToArray());

        Assert.True(result.Success, result.Error);
        Assert.True(canonicalResult.Success, canonicalResult.Error);
        Assert.Contains("changed=0 added=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("duplicate_modules=1 replaced_registrations=5 reattested_modules=4", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);
        Assert.Equal(canonical.AllPublishedBytes(), fixture.AllPublishedBytes());
        Assert.Equal(stateBefore, fixture.StateBytes());
        Assert.Equal(stableA, fixture.EventBytes("A"));
        Assert.Equal(stableU, fixture.EventBytes("U"));
        Assert.Equal(modules.Length, fixture.StateFileCount());
        var after = ReadRepairEvents(fixture.AcceptedFiles());
        var strict = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            fixture.AcceptedFiles().ToImmutableDictionary(static file => file.Path)));
        Assert.Equal(modules.Length, strict.ActiveByPath.Count);
        Assert.Equal(after.Length, after.Select(static item => item.DescriptorPath).Distinct().Count());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(after, [], out _));
        AssertPrerequisite(after, "B", "A");
        AssertPrerequisite(after, "C", "B");
        AssertPrerequisite(after, "D", "B");
        AssertPrerequisite(after, "E", "C");
        AssertRepairAdmission(modules, catalog, duplicates, fixture.AcceptedFiles());
        var repairedBytes = fixture.AllPublishedBytes();
        var second = fixture.AlignWithAcceptedWritesDenied();
        Assert.True(second.Success, second.Error);
        Assert.Equal(repairedBytes, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData("statement")]
    [InlineData("declaration")]
    [InlineData("state")]
    [InlineData("missing-state")]
    [InlineData("descendant")]
    [InlineData("prerequisite")]
    [InlineData("axiom")]
    public void DuplicateRepairRejectsIdentityOrTrustConflictsWithoutPublishing(string conflict)
    {
        var modules = DuplicateRepairModules();
        var catalog = BuildCatalog(modules);
        var files = DuplicateEvents(catalog);
        var events = ReadRepairEvents(files);
        if (conflict is "statement" or "declaration" or "descendant")
        {
            var name = conflict == "descendant" ? "C" : "B";
            var old = events.First(item => item.DescriptorPath == RepoPathFor(name));
            var material = catalog.ByPath[RepoPathFor(name)] with
            {
                PrerequisiteFrozenNodeIds = old.Payload.GetProperty("prerequisite_frozen_node_ids")
                    .EnumerateArray().Select(item => FrozenNodeId.Create(item.GetString()!)).ToImmutableArray(),
            };
            material = conflict == "declaration"
                ? material with { DeclarationStatementIds = material.DeclarationStatementIds.Select(item => item with
                    { StatementId = StatementId.Create(Sha256("conflicting declaration")) }).ToImmutableArray() }
                : material with { StatementId = StatementId.Create(Sha256("conflicting statement")) };
            files = files.Where(file => file.Path != old.SourcePath).Append(
                EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                    FrozenLedgerCanonicalWriter.FreezePayload(material)))).ToImmutableArray();
        }
        if (conflict == "prerequisite") modules[0] = modules[0] with { StatementMaterial = "True = True" };
        if (conflict == "axiom") modules[1] = modules[1] with { Axioms = ["UnsafeAxiom"] };
        using var fixture = new AlignFixture(modules);
        fixture.InstallAccepted(files);
        foreach (var module in modules.Where(module => conflict != "missing-state" || module.Name != "B"))
            fixture.InstallState(module.Name, catalog.ByPath[RepoPathFor(module.Name)].StatementId);
        if (conflict == "state") fixture.InstallState("B", StatementId.Create(Sha256("conflicting pin")));
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align(DuplicateRepairOptions());

        Assert.False(result.Success);
        Assert.Equal(before, fixture.AllPublishedBytes());
        Assert.False(fixture.HasPublicationStaging());
    }

    [Fact]
    public void DuplicateRepairRequiresExplicitRecordedDescendantsBeforePublishing()
    {
        var modules = DuplicateRepairModules();
        var catalog = BuildCatalog(modules);
        using var fixture = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, catalog, DuplicateEvents(catalog));
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align("--repair-duplicate-registration", PathFor("B"));

        Assert.False(result.Success);
        Assert.Contains("descendants require explicit --selector", result.Error, StringComparison.Ordinal);
        foreach (var name in new[] { "C", "D", "E" })
            Assert.Contains("--selector " + PathFor(name), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DuplicateRepairRequiresCurrentImportDescendantOutsideScopedReport()
    {
        var modules = DuplicateRepairModules();
        modules[^1] = DuplicateRepairModule("U", "B");
        var catalog = BuildCatalog(modules);
        var files = DuplicateEvents(catalog);
        var oldU = ReadRepairEvents(files).Single(item => item.DescriptorPath == RepoPathFor("U"));
        files = files.Where(file => file.Path != oldU.SourcePath).Append(EventFile("Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(FrozenLedgerCanonicalWriter.FreezePayload(
                catalog.ByPath[RepoPathFor("U")] with { PrerequisiteFrozenNodeIds = [] })))).ToImmutableArray();
        using var fixture = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, catalog, files);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align(DuplicateRepairOptions());

        Assert.False(result.Success);
        Assert.Contains("--selector " + PathFor("U"), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DuplicateRepairReattestsRecordedDescendantWhoseCurrentImportWasRemoved()
    {
        var modules = DuplicateRepairModules();
        var oldCatalog = BuildCatalog(modules);
        modules[3] = Module("D");
        using var fixture = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, oldCatalog, DuplicateEvents(oldCatalog));
        var stateBefore = fixture.StateBytes();

        var result = fixture.Align(DuplicateRepairOptions());

        Assert.True(result.Success, result.Error);
        var events = ReadRepairEvents(fixture.AcceptedFiles());
        Assert.Empty(events.Single(item => item.DescriptorPath == RepoPathFor("D"))
            .Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        Assert.True(DagLedgerLoader.TryOrderClosedDag(events, [], out _));
        Assert.Equal(stateBefore, fixture.StateBytes());
    }

    [Fact]
    public void DuplicateRepairRejectsUnrelatedDanglingDagWithoutPublishing()
    {
        var modules = DuplicateRepairModules();
        var catalog = BuildCatalog(modules);
        var files = DuplicateEvents(catalog);
        var oldU = ReadRepairEvents(files).Single(item => item.DescriptorPath == RepoPathFor("U"));
        files = files.Where(file => file.Path != oldU.SourcePath).Append(EventFile("Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(FrozenLedgerCanonicalWriter.FreezePayload(
                catalog.ByPath[RepoPathFor("U")] with
                { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("missing unrelated prerequisite"))] })))).ToImmutableArray();
        using var fixture = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, catalog, files);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align(DuplicateRepairOptions());

        Assert.False(result.Success);
        Assert.Contains("does not form a closed dependency DAG", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    [Fact]
    public void DuplicateRepairRollsBackDisplacedEventsOnPublicationFailure()
    {
        var modules = DuplicateRepairModules();
        var catalog = BuildCatalog(modules);
        var files = DuplicateEvents(catalog);
        using var fixture = new AlignFixture(modules);
        using var canonical = new AlignFixture(modules);
        InstallDuplicateFixture(fixture, catalog, files);
        var expected = canonical.Align(modules.SelectMany(module => new[] { "--add", PathFor(module.Name) }).ToArray());
        Assert.True(expected.Success, expected.Error);
        var oldPaths = files.Select(static file => file.Path).ToHashSet();
        var obstruction = canonical.AcceptedFiles().First(file => !oldPaths.Contains(file.Path));
        fixture.BlockAcceptedPublication(obstruction.Path);
        var before = fixture.AllPublishedBytes();

        var result = fixture.Align(DuplicateRepairOptions());

        Assert.False(result.Success);
        Assert.DoesNotContain("rollback was incomplete", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
        Assert.False(fixture.HasPublicationStaging());
    }

    private static ModuleSpec[] DuplicateRepairModules() =>
    [
        Module("A"), DuplicateRepairModule("B", "A"), DuplicateRepairModule("C", "B"),
        DuplicateRepairModule("D", "B"), DuplicateRepairModule("E", "C"), Module("U"),
    ];

    private static ModuleSpec DuplicateRepairModule(string name, params string[] imports) =>
        Module(name, string.Concat(imports.Select(static dependency => $"import D5.S0.Carrier.{dependency}\n"))
            + Source(name), imports: imports);

    private static string[] DuplicateRepairOptions() =>
    [
        "--repair-duplicate-registration", PathFor("B"),
        "--selector", PathFor("C"), "--selector", PathFor("D"), "--selector", PathFor("E"),
    ];

    private static void InstallDuplicateFixture(
        AlignFixture fixture, FrozenMaterialCatalog catalog, IEnumerable<RepositoryFile> files)
    {
        fixture.InstallAccepted(files);
        foreach (var material in catalog.ClosedNodes)
            fixture.InstallState(Path.GetFileNameWithoutExtension(material.RepoPath.Value), material.StatementId);
    }

    private static ImmutableArray<RepositoryFile> DuplicateEvents(FrozenMaterialCatalog catalog)
    {
        var aFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("A")])));
        var a = Assert.Single(ReadRepairEvents([aFile]));
        var b = catalog.ByPath[RepoPathFor("B")];
        var bFirst = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(b with { PrerequisiteFrozenNodeIds = [a.FrozenNodeId] })));
        var bSecond = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(b with
            { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256("obsolete prerequisite"))] })));
        var cFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("C")] with
            { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Assert.Single(ReadRepairEvents([bFirst])).EventHash)] })));
        var dFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("D")] with
            { PrerequisiteFrozenNodeIds = [Assert.Single(ReadRepairEvents([bSecond])).FrozenNodeId] })));
        var eFile = EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("E")] with
            { PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Assert.Single(ReadRepairEvents([cFile])).EventHash)] })));
        return [aFile, bFirst, bSecond, cFile, dFile, eFile,
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(catalog.ByPath[RepoPathFor("U")])))];
    }
}
