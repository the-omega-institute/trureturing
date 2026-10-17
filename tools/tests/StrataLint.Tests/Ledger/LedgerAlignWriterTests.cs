using System.Collections.Immutable;
using System.IO.Compression;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerAlignWriterTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingExplicitModuleSelectionIsRejectedWithoutReadsOrWrites(bool hasFrozenMembers)
    {
        var original = Module("A");
        using var fixture = new AlignFixture(original with { StatementMaterial = "A changed" });
        if (hasFrozenMembers) fixture.Install(BuildCatalog(original));
        var before = fixture.Image();

        var result = fixture.Align();

        Assert.False(result.Success);
        Assert.Contains("USAGE", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, fixture.Repository.ReadCount);
        Assert.Equal(before, fixture.Image());
    }

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
    [InlineData(false)]
    [InlineData(true)]
    public void FullOrScopedBundleAddsOnlySelectedOwner(bool scoped)
    {
        var a = Module("A", source: "import D5.S0.Carrier.B\ntheorem a : True := by trivial\n", imports: ["B"]);
        var b = Module("B");
        var c = Module("C") with { StatementMaterial = "True = True" };
        using var fixture = new AlignFixture(a, b, c);
        var path = fixture.ReportPath(scoped, "--add", PathFor("A"));

        var result = fixture.Invoke(["--add", PathFor("A"), "--candidate-lean-report", path]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("added=1", result.Output, StringComparison.Ordinal);
        var expected = StateFiles(BuildCatalog(a, b, c)).Single(file => file.Path ==
            FrozenStatePath.FromModulePath(RepoPathFor("A")));
        Assert.Equal(expected.RawBytes.ToArray(), File.ReadAllBytes(fixture.StateFile("A")));
        Assert.Equal(expected.Path.Value, Assert.Single(fixture.Image()).Key);
    }

    [Theory]
    [InlineData("source", "source hash does not match D5/S0/Carrier/C.lean")]
    [InlineData("material", "Lean statement material hash mismatch")]
    [InlineData("imports", "imports must be sorted and unique")]
    public void FullBundleRejectsUnselectedCorruptionBeforeAnyWrite(string defect, string expectedError)
    {
        using var fixture = new AlignFixture(Module("A"), Module("C") with { StatementMaterial = "True = True" });
        var path = fixture.ReportPath(scoped: false, "--add", PathFor("A"));
        fixture.Corrupt(path, "C", defect);

        AssertRejectedBeforeAnyWrite(fixture, path, expectedError, defect is "material" or "statement");
    }

    [Theory]
    [InlineData(false, "source", "source hash does not match D5/S0/Carrier/A.lean")]
    [InlineData(true, "source", "source hash does not match D5/S0/Carrier/A.lean")]
    [InlineData(false, "material", "Lean statement material hash mismatch")]
    [InlineData(true, "material", "Lean statement material hash mismatch")]
    [InlineData(false, "source-imports", "imports do not match source")]
    [InlineData(true, "source-imports", "imports do not match source")]
    [InlineData(false, "statement", "statement identity does not match material")]
    [InlineData(true, "statement", "statement identity does not match material")]
    [InlineData(false, "axioms", "expected Closed")]
    [InlineData(true, "axioms", "expected Closed")]
    public void FullOrScopedBundleRetainsSelectedValidationBeforeAnyWrite(bool scoped, string defect, string expectedError)
    {
        using var fixture = new AlignFixture(Module("A"), Module("C") with { StatementMaterial = "True = True" });
        var path = fixture.ReportPath(scoped, "--add", PathFor("A"));
        fixture.Corrupt(path, "A", defect);

        AssertRejectedBeforeAnyWrite(fixture, path, expectedError, defect is "material" or "statement");
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

    private static void AssertRejectedBeforeAnyWrite(AlignFixture fixture, string path, string expectedError, bool invalidData)
    {
        string error;
        if (invalidData)
            error = Assert.Throws<InvalidDataException>(() =>
                fixture.Invoke(["--add", PathFor("A"), "--candidate-lean-report", path])).Message;
        else
        {
            var result = fixture.Invoke(["--add", PathFor("A"), "--candidate-lean-report", path]);
            Assert.False(result.Success);
            error = result.Error;
        }
        Assert.Contains(expectedError, error, StringComparison.Ordinal);
        Assert.Empty(fixture.Image());
        Assert.False(Directory.Exists(Path.GetDirectoryName(fixture.StateFile("A"))));
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
            report = LeanAxiomReport.Create(Report(modules).Files.ToDictionary(
                static item => item.Key.Value, item => item.Value with
                { Imports = LeanSourceCatalog.ParseFileImports(snapshot.Files[item.Key], includeImplicitInit: true) }));
            fullReport = Path.Combine(temporary.Path, "full.json");
            RawLeanReportArtifact.WriteFile(fullReport, snapshot, report);
            Repository = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        }
        internal CommandResult Invoke(string[] arguments) => DagLedgerAlignWriter.Align(temporary.Path, Repository, arguments);
        internal CommandResult Align(params string[] options) =>
            Invoke([.. options, "--candidate-lean-report", ReportPath(scoped: true, options)]);
        internal string ReportPath(bool scoped, params string[] options)
        {
            var targets = options.Select((option, index) => (option, index))
                .Where(static item => item.option is "--selector" or "--add")
                .Select(item => RepoPath.CreateKnown(options[item.index + 1])).ToArray();
            var reportPath = fullReport;
            if (scoped && targets.Length > 0 && targets.All(snapshot.Files.ContainsKey))
            {
                var scope = LeanReportScope.Create(snapshot, targets);
                var selected = RepositorySnapshot.Create(snapshot.Files.Where(item => scope.Paths.Contains(item.Key)).ToImmutableDictionary());
                var selectedReport = LeanAxiomReport.Create(report.Files.Where(item => scope.Paths.Contains(item.Key)).ToDictionary(
                    static item => item.Key.Value, static item => item.Value));
                reportPath = Path.Combine(temporary.Path, "scoped.json");
                RawLeanReportArtifact.WriteFile(reportPath, selected, selectedReport);
                File.WriteAllText(reportPath, File.ReadAllText(reportPath).Replace(RawLeanReportArtifact.Schema, RawLeanReportArtifact.ScopedSchema, StringComparison.Ordinal));
            }
            return reportPath;
        }
        internal void Corrupt(string path, string name, string defect)
        {
            if (defect == "material")
            {
                var address = report.Files[RepoPathFor(name)].Declarations[0].StatementTypeAddress;
                using var archive = ZipFile.Open(RawLeanReportArtifact.MaterialsPath(path), ZipArchiveMode.Update);
                using var stream = archive.GetEntry("sha256/" + address[7..])!.Open();
                stream.SetLength(0);
                stream.Write(Encoding.UTF8.GetBytes("corrupt material"));
                return;
            }
            var document = JsonNode.Parse(File.ReadAllText(path))!;
            var module = document["modules"]!.AsArray().Single(item => item!["source_path"]!.GetValue<string>() == PathFor(name))!;
            switch (defect)
            {
                case "source": module["source_sha256"] = "sha256:" + new string('0', 64); break;
                case "imports": module["imports"] = new JsonArray("Init", "Init"); break;
                case "source-imports": module["imports"] = new JsonArray("Mathlib"); break;
                case "statement": module["declarations"]![0]!["statement_id"] = "sha256:" + new string('0', 64); break;
                case "axioms": module["declarations"]![0]!["axioms"] = new JsonArray("sorryAx"); break;
                default: throw new ArgumentException("unknown fixture defect", nameof(defect));
            }
            File.WriteAllBytes(path, StructuredCanonicalWriter.WriteJson(document.ToJsonString()).ToArray());
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
