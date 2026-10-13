using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class MathlibCompletedRetirementTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CompletedPairedRetirementValidatesAllRetainedOwnersWithoutWriting(bool unchangedStatements)
    {
        using var fixture = new Fixture(unchangedStatements ? "no-drift" : "valid");
        var before = fixture.Image();
        var result = fixture.Reanchor();
        Assert.True(result.Success, result.Error);
        Assert.Contains("retired_upstream_ports=1 published_modules=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("validated_retained_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Equal(before, fixture.Image());
    }

    [Theory]
    [InlineData("source-present")]
    [InlineData("state-present")]
    [InlineData("unlisted-retirement")]
    [InlineData("unfrozen-import")]
    [InlineData("unfrozen-Reg-import")]
    [InlineData("retained-import")]
    [InlineData("same-pin")]
    [InlineData("weakened-statement")]
    [InlineData("changed-definition-with-same-type")]
    [InlineData("nonstandard-axiom")]
    [InlineData("stale-state")]
    [InlineData("malformed-state")]
    public void IncompleteOrUnauthorizedPublicationIsRejectedWithoutWriting(string defect)
    {
        using var fixture = new Fixture(defect);
        var before = fixture.Image();
        var result = fixture.Reanchor();
        Assert.False(result.Success);
        if (defect == "unfrozen-Reg-import")
            Assert.Contains("still imports", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.Image());
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("non-D5")]
    [InlineData("unknown-option")]
    public void InvalidRetirementArgumentsAreRejectedBeforeReading(string defect)
    {
        using var fixture = new Fixture("valid");
        string[] arguments = defect switch
        {
            "missing" => ["--retired-upstream-port"],
            "duplicate" => ["--retired-upstream-port", PathFor("A"), "--retired-upstream-port", PathFor("A")],
            "non-D5" => ["--retired-upstream-port", "Reg/Support/A.lean"],
            _ => ["--unknown", PathFor("A")],
        };
        var result = fixture.Invoke(arguments);
        Assert.False(result.Success);
        Assert.Equal(0, fixture.Repository.ReadCount);
    }

    [Fact]
    public void AnUnregisteredRetirementAndAnUnannouncedMissingOwnerAreBothRejected()
    {
        using var fixture = new Fixture("valid");
        Assert.False(fixture.Invoke(["--retired-upstream-port", PathFor("Unknown")]).Success);
        Assert.False(fixture.Invoke([]).Success);
    }

    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly FakeLeanReportSource source;
        internal FakeRepositoryGateway Repository { get; }

        internal Fixture(string defect)
        {
            var oldA = Module("A");
            var oldB = ModuleWithReport("B", defect == "weakened-statement"
                ? "theorem b : False := by contradiction\n" : "theorem b : True := by trivial\n", "old B");
            var newB = ModuleWithReport("B", defect == "retained-import"
                ? "import D5.S0.Carrier.A\ntheorem b : True := by trivial\n" : "theorem b : True := by trivial\n",
                defect == "no-drift" ? oldB.StatementMaterial : "new B",
                axioms: defect == "nonstandard-axiom" ? ["userAxiom"] : []);
            if (defect == "changed-definition-with-same-type")
            {
                oldB = ModuleWithReport("B", "def b : Prop := False\n", "Prop", kind: "def");
                newB = ModuleWithReport("B", "def b : Prop := True\n", "Prop", kind: "def");
            }
            var currentModules = new List<ModuleSpec> { newB };
            if (defect == "source-present") currentModules.Add(oldA);
            if (defect == "unfrozen-import") currentModules.Add(Module("C",
                "import D5.S0.Carrier.A\ntheorem c : True := by trivial\n", imports: ["A"]));
            var baseline = Files([oldA, oldB], StateFiles(BuildCatalog(oldA, oldB)), upgraded: false);
            var registeredB = defect == "stale-state" ? oldB : newB with { Axioms = [] };
            var stateFiles = StateFiles(BuildCatalog(registeredB));
            if (defect == "state-present") stateFiles = stateFiles.AddRange(StateFiles(BuildCatalog(oldA)));
            if (defect == "unlisted-retirement") stateFiles = [];
            if (defect == "malformed-state") stateFiles = [TextFile(stateFiles[0].Path.Value, "not JSON\n")];
            var current = Files(currentModules, stateFiles, upgraded: defect != "same-pin");
            if (defect == "unfrozen-Reg-import")
                current = current.Add(TextFile("Reg/Support/Outside.lean",
                    "import D5.S0.Carrier.A\nexample : True := by trivial\n"));
            var snapshot = RepositorySnapshot.Create(current.ToImmutableDictionary(static file => file.Path));
            var report = Report(currentModules.ToArray());
            report = LeanAxiomReport.Create(report.Files.ToDictionary(static pair => pair.Key.Value,
                pair => pair.Value with
                { Imports = LeanSourceCatalog.ParseFileImports(snapshot.Files[pair.Key], includeImplicitInit: true) }));
            source = new(report);
            Repository = new(RawChangeSet.Create([]), Raw(current), Raw(baseline));
            foreach (var file in stateFiles)
            {
                var path = Path.Combine(temporary.Path, file.Path.Value);
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllBytes(path, file.RawBytes.AsSpan().ToArray());
            }
        }

        internal CommandResult Reanchor() => Invoke(["--retired-upstream-port", PathFor("A")]);
        internal CommandResult Invoke(string[] tail) => DagLedgerMathlibReanchorWriter.Reanchor(
            temporary.Path, Repository, source, ["--base", "baseline", .. tail]);
        internal Dictionary<string, string> Image() => Directory.EnumerateFiles(temporary.Path, "*", SearchOption.AllDirectories)
            .ToDictionary(path => Path.GetRelativePath(temporary.Path, path).Replace('\\', '/'), File.ReadAllText, StringComparer.Ordinal);
        public void Dispose() => temporary.Dispose();

        private static ImmutableArray<RepositoryFile> Files(IEnumerable<ModuleSpec> modules,
            ImmutableArray<RepositoryFile> states, bool upgraded) => modules
            .Select(module => TextFile(PathFor(module.Name), module.Source)).Concat(states)
            .Append(TextFile("lean-toolchain", upgraded ? "leanprover/lean4:v4.25.0\n" : "leanprover/lean4:v4.24.0\n"))
            .Append(TextFile("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\""
                + new string(upgraded ? 'b' : 'a', 40) + "\"}]}\n")).ToImmutableArray();
        private static RepositoryFile TextFile(string path, string text) => new(RepoPath.CreateKnown(path),
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)), text);
        private static RawRepositorySnapshot Raw(IEnumerable<RepositoryFile> files) => RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Path.Value, file.Text)));
    }
}
