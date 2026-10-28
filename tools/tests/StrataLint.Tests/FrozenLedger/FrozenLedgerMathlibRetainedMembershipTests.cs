using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MathlibReanchorWriterUpdatesRetainedMemberWithoutRestoringExitedMember(bool retainSource)
    {
        var oldA = ModuleWithReport("A", "theorem a : True := by trivial\n", statementMaterial: "old True");
        var newA = oldA with { StatementMaterial = "new True" };
        var b = Module("B");
        var baseline = ReanchorSnapshot([oldA, b], [oldA, b], candidate: false);
        var current = ReanchorSnapshot([oldA], retainSource ? [newA, b] : [newA], candidate: true);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw(current), Raw(baseline));
        var report = Report(newA);
        var source = new FakeLeanReportSource(report);
        using var directory = new TemporaryDirectory();
        MaterializeStates(directory.Path, current);

        var result = DagLedgerMathlibReanchorWriter.Reanchor(directory.Path, gateway, source, ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var path = System.IO.Path.Combine(directory.Path, FrozenStatePath.FromModulePath(RepoPathFor("A")).Value);
        var written = FrozenStateRecordLoader.Load(TextFile(FrozenStatePath.FromModulePath(RepoPathFor("A")).Value,
            System.IO.File.ReadAllText(path)));
        var expected = FrozenStateRecord.FromReport(RepoPathFor("A"), report.Files[RepoPathFor("A")]);
        Assert.Equal(expected.StatementId, written.StatementId);
        Assert.Equal(FrozenStateRecord.Encode(expected.StatementId, expected.Declarations).ToArray(),
            System.IO.File.ReadAllBytes(path));
        Assert.False(System.IO.File.Exists(System.IO.Path.Combine(directory.Path,
            FrozenStatePath.FromModulePath(RepoPathFor("B")).Value)));
        Assert.Equal(1, source.CallCount);
        Assert.Equal(1, gateway.ReadCurrentCount);
    }

    [Fact]
    public void MathlibReanchorWriterWithNoRetainedMembersDoesNotRequestAnEmptyReport()
    {
        var b = Module("B");
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]),
            Raw(ReanchorSnapshot([], [], candidate: true)),
            Raw(ReanchorSnapshot([b], [b], candidate: false)));
        var source = new FakeLeanReportSource(null);
        using var directory = new TemporaryDirectory();

        var result = DagLedgerMathlibReanchorWriter.Reanchor(directory.Path, gateway, source, ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, source.CallCount);
        Assert.Empty(System.IO.Directory.EnumerateFileSystemEntries(directory.Path));
    }

    [Theory]
    [InlineData("missing-source")]
    [InlineData("missing-report")]
    [InlineData("malformed-state")]
    public void MathlibReanchorWriterRejectsInvalidRetainedMembersWithoutWriting(string defect)
    {
        var a = Module("A");
        var b = Module("B");
        var baseline = ReanchorSnapshot([a, b], [a, b], candidate: false);
        var current = ReanchorSnapshot([a, b], defect == "missing-source" ? [a] : [a, b], candidate: true);
        if (defect == "malformed-state") current = Snapshot(current.Files.Values
            .Where(file => file.Path != FrozenStatePath.FromModulePath(RepoPathFor("B")))
            .Append(TextFile(FrozenStatePath.FromModulePath(RepoPathFor("B")).Value, "{}")));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw(current), Raw(baseline));
        var source = new FakeLeanReportSource(defect == "missing-report" ? Report(a) : Report(a, b));
        using var directory = new TemporaryDirectory();
        MaterializeStates(directory.Path, current);
        var before = current.Files.Values.Where(file => FrozenStatePath.IsUnderRoot(file.Path.Value))
            .ToDictionary(file => file.Path.Value, file => System.IO.File.ReadAllText(System.IO.Path.Combine(directory.Path, file.Path.Value)));

        var result = DagLedgerMathlibReanchorWriter.Reanchor(directory.Path, gateway, source, ["--base", "baseline"]);

        Assert.False(result.Success);
        foreach (var (path, text) in before)
            Assert.Equal(text, System.IO.File.ReadAllText(System.IO.Path.Combine(directory.Path, path)));
    }

    [Theory]
    [InlineData("none", true)]
    [InlineData("missing-retained-report", false)]
    [InlineData("nonstandard-retained-axiom", false)]
    [InlineData("exited-target", false)]
    [InlineData("new-target", false)]
    public void MathlibReanchorAuthorizationChecksEveryRetainedMemberAndRejectsOtherTargets(string defect, bool expected)
    {
        var a = ModuleWithReport("A", "theorem a : True := by trivial\n", statementMaterial: "old True");
        var changed = a with { StatementMaterial = "new True" };
        var b = Module("B");
        var c = Module("C");
        var d = Module("D");
        var baseline = ReanchorSnapshot([a, b, d], [a, b, d], candidate: false);
        var current = ReanchorSnapshot([a, b, c], [changed, b, c, d], candidate: true);
        var report = Report(changed, b, c, d);
        if (defect == "missing-retained-report") report = Report(changed, c);
        if (defect == "nonstandard-retained-axiom") report = LeanAxiomReport.Create(report.Files.ToDictionary(
            pair => pair.Key.Value, pair => pair.Key == RepoPathFor("B") ? pair.Value with
            { Declarations = pair.Value.Declarations.Select(declaration => declaration with { Axioms = ["sorryAx"] }).ToImmutableArray() }
            : pair.Value));
        var target = defect == "exited-target" ? "D" : defect == "new-target" ? "C" : "A";

        var authorized = new MathlibUpgradeFrozenLedgerReplacementAuthorization(baseline, current)
            .IsAuthorized([RepoPathFor(target)], FrozenStateCatalog.Load(baseline), report);

        Assert.Equal(expected, authorized);
    }

    [Theory]
    [InlineData(false, true)]
    [InlineData(true, false)]
    public void MathlibReanchorStillComparesDependenciesAfterTheirFrozenMembershipExits(bool weakenDependency, bool expected)
    {
        var dependency = ModuleWithReport("B", "def p : Prop := True\n", statementMaterial: "Prop",
            declarations: ["p"], kind: "def");
        var a = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : p := by trivial\n",
            statementMaterial: "old p") with { Imports = ["B"] };
        var changed = a with { StatementMaterial = "new p" };
        var newDependency = weakenDependency ? dependency with { Source = "def p : Prop := False\n" } : dependency;
        var baseline = ReanchorSnapshot([a, dependency], [a, dependency], candidate: false);
        var current = ReanchorSnapshot([a], [changed, newDependency], candidate: true);

        var authorized = new MathlibUpgradeFrozenLedgerReplacementAuthorization(baseline, current)
            .IsAuthorized([RepoPathFor("A")], FrozenStateCatalog.Load(baseline), Report(changed, newDependency));

        Assert.Equal(expected, authorized);
    }

    private static RepositorySnapshot ReanchorSnapshot(ModuleSpec[] members, ModuleSpec[] sources, bool candidate) =>
        Snapshot(StateFiles(BuildCatalog(members)).AddRange(ReanchorInputFiles(sources, ReanchorEnvironment.PinUpgrade, candidate)));

    private static RawRepositorySnapshot Raw(RepositorySnapshot snapshot) => RawRepositorySnapshot.Create(
        snapshot.Files.Values.Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes)));

    private static void MaterializeStates(string root, RepositorySnapshot snapshot)
    {
        foreach (var file in snapshot.Files.Values.Where(file => FrozenStatePath.IsUnderRoot(file.Path.Value)))
        {
            var path = System.IO.Path.Combine(root, file.Path.Value);
            System.IO.Directory.CreateDirectory(System.IO.Path.GetDirectoryName(path)!);
            System.IO.File.WriteAllBytes(path, file.RawBytes.ToArray());
        }
    }
}
