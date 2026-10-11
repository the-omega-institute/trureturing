using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerAlignWriterTests
{
    [Fact]
    public void RepinWritesOnlyTargetWithFrozenDownstreamAndIdenticalRetryWritesNothing()
    {
        var original = Module("A");
        var current = original with { StatementMaterial = "True = True" };
        var downstream = Module("B", source: "import D5.S0.Carrier.A\ntheorem b : True := by trivial\n", imports: ["A"]);
        using var fixture = new AlignFixture(current, downstream);
        fixture.Install(BuildCatalog(original, downstream));
        var before = fixture.Image();
        var result = fixture.Align("--selector", PathFor("A"));
        Assert.True(result.Success, result.Error);
        var after = fixture.Image();
        Assert.Equal([FrozenStatePath.FromModulePath(RepoPathFor("A")).Value],
            after.Keys.Where(path => before[path] != after[path]));
        var timestamp = File.GetLastWriteTimeUtc(fixture.StateFile("A"));
        var retry = fixture.Align("--selector", PathFor("A"));
        Assert.True(retry.Success, retry.Error);
        Assert.Contains("changed=0", retry.Output, StringComparison.Ordinal);
        Assert.Equal(timestamp, File.GetLastWriteTimeUtc(fixture.StateFile("A")));
        Assert.Equal(after, fixture.Image());
    }

    [Fact]
    public void DifferentModulesHaveDisjointWriteSets()
    {
        var oldA = Module("A");
        var oldB = Module("B");
        using var first = new AlignFixture(oldA with { StatementMaterial = "A changed" }, oldB);
        using var second = new AlignFixture(oldA, oldB with { StatementMaterial = "B changed" });
        var baseline = BuildCatalog(oldA, oldB);
        first.Install(baseline); second.Install(baseline);
        var beforeFirst = first.Image(); var beforeSecond = second.Image();
        Assert.True(first.Align("--selector", PathFor("A")).Success);
        Assert.True(second.Align("--selector", PathFor("B")).Success);
        var writesA = first.Image().Where(pair => beforeFirst[pair.Key] != pair.Value).Select(static pair => pair.Key).ToArray();
        var writesB = second.Image().Where(pair => beforeSecond[pair.Key] != pair.Value).Select(static pair => pair.Key).ToArray();
        Assert.Single(writesA); Assert.Single(writesB); Assert.Empty(writesA.Intersect(writesB));
    }

    [Fact]
    public void ScopedAddAllowsClosedUnregisteredImportsAndIgnoresUnrelatedOpenModule()
    {
        var a = Module("A", source: "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n", imports: ["B"]);
        using var fixture = new AlignFixture(a, Module("B"), Module("C", axioms: ["sorryAx"]));
        var result = fixture.Align("--add", PathFor("A"));
        Assert.True(result.Success, result.Error);
        Assert.Single(fixture.Image());
        Assert.True(File.Exists(fixture.StateFile("A")));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("open")]
    [InlineData("unregistered")]
    [InlineData("duplicate")]
    public void InvalidSelectionWritesNothing(string mode)
    {
        using var fixture = new AlignFixture(mode == "open" ? Module("A", axioms: ["sorryAx"]) : Module("A"));
        var result = mode switch
        {
            "missing" => fixture.Align("--add", PathFor("Missing")),
            "open" => fixture.Align("--add", PathFor("A")),
            "unregistered" => fixture.Align("--selector", PathFor("A")),
            _ => fixture.Align("--add", PathFor("A"), "--add", PathFor("A")),
        };
        Assert.False(result.Success); Assert.Empty(fixture.Image());
    }

    [Fact]
    public void OldStateSchemaFailsClosedBeforeAnyWrite()
    {
        using var fixture = new AlignFixture(Module("A"));
        fixture.Install(BuildCatalog(Module("A")));
        File.WriteAllText(fixture.StateFile("A"), "{\"statement_id\":\"" + Sha256("old pin") + "\"}\n");
        var before = fixture.Image();
        Assert.False(fixture.Align("--selector", PathFor("A")).Success);
        Assert.Equal(before, fixture.Image());
    }

    [Fact]
    public void RetirementKeepsOtherMembersAndRequiresSourceAbsence()
    {
        using var fixture = new AlignFixture(Module("B"));
        fixture.Install(BuildCatalog(Module("A"), Module("B")));
        var before = File.ReadAllBytes(fixture.StateFile("B"));
        Assert.False(fixture.Align("--retire-registration", PathFor("B")).Success);
        var result = fixture.Align("--retire-registration", PathFor("A"));
        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(fixture.StateFile("A")));
        Assert.Equal(before, File.ReadAllBytes(fixture.StateFile("B")));
    }

    [Theory]
    [InlineData("--from-accepted")]
    [InlineData("--retire-registration")]
    public void RetiredOrIncompleteArgumentsAreRejectedBeforeReads(string argument)
    {
        using var fixture = new AlignFixture();
        Assert.False(fixture.Invoke([argument]).Success);
        Assert.Equal(0, fixture.Repository.ReadCount);
    }

    private sealed class AlignFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly RepositorySnapshot snapshot;
        private readonly LeanAxiomReport report;
        private readonly string fullReport;
        internal FakeRepositoryGateway Repository { get; }
        internal AlignFixture(params ModuleSpec[] modules)
        {
            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n", ["lake-manifest.json"] = "{}\n",
            };
            foreach (var module in modules) files[PathFor(module.Name)] = module.Source;
            var raw = RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
            snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
            report = Report(modules);
            fullReport = Path.Combine(temporary.Path, "full.json");
            RawLeanReportArtifact.WriteFile(fullReport, snapshot, report);
            Repository = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        }
        internal CommandResult Invoke(string[] arguments) => DagLedgerAlignWriter.Align(temporary.Path, Repository, arguments);
        internal CommandResult Align(params string[] options)
        {
            var targets = options.Select((option, index) => (option, index))
                .Where(static item => item.option is "--selector" or "--add")
                .Select(item => RepoPath.CreateKnown(options[item.index + 1])).ToArray();
            var reportPath = fullReport;
            if (targets.Length > 0 && targets.All(snapshot.Files.ContainsKey))
            {
                var scope = LeanReportScope.Create(snapshot, targets);
                var selected = RepositorySnapshot.Create(snapshot.Files.Where(item => scope.Paths.Contains(item.Key)).ToImmutableDictionary());
                var selectedReport = LeanAxiomReport.Create(report.Files.Where(item => scope.Paths.Contains(item.Key)).ToDictionary(
                    static item => item.Key.Value, item => item.Value with
                    { Imports = LeanSourceCatalog.ParseFileImports(snapshot.Files[item.Key], includeImplicitInit: true) }));
                reportPath = Path.Combine(temporary.Path, "scoped.json");
                RawLeanReportArtifact.WriteFile(reportPath, selected, selectedReport);
                File.WriteAllText(reportPath, File.ReadAllText(reportPath).Replace(RawLeanReportArtifact.Schema, RawLeanReportArtifact.ScopedSchema, StringComparison.Ordinal));
            }
            return Invoke([.. options, "--candidate-lean-report", reportPath]);
        }
        internal void Install(FrozenMaterialCatalog catalog)
        {
            foreach (var file in StateFiles(catalog))
            {
                var path = Path.Combine(temporary.Path, file.Path.Value);
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllBytes(path, file.RawBytes.AsSpan().ToArray());
            }
        }
        internal string StateFile(string name) => Path.Combine(temporary.Path, FrozenStatePath.FromModulePath(RepoPathFor(name)).Value);
        internal Dictionary<string, string> Image()
        {
            var root = Path.Combine(temporary.Path, FrozenStatePath.Root);
            return Directory.Exists(root) ? Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories)
                .ToDictionary(path => Path.GetRelativePath(temporary.Path, path).Replace('\\', '/'), File.ReadAllText, StringComparer.Ordinal)
                : new(StringComparer.Ordinal);
        }
        public void Dispose() => temporary.Dispose();
    }
}
