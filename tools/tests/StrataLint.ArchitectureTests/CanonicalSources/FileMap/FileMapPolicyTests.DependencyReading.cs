using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void DependencyInspectionHandlesLargeUnrelatedDataAgainstCompleteGeneratedIndex()
    {
        var manifest = Parse(
            Entry("Data/**/*.json", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"));
        const string input = "Data/input.json";
        var paths = Enumerable.Range(0, 8192).Select(index => $"Generated/{index:D5}.json")
            .Append(input).ToArray();
        var source = new string('x', 32 * 1024 * 1024);
        var reads = new List<string>();

        var findings = FileMapPolicy.InspectDependencies(manifest, paths, path =>
        {
            reads.Add(path);
            return source;
        }, new HashSet<string>([input], StringComparer.Ordinal));

        Assert.Empty(findings);
        Assert.Equal(new[] { input }, reads);
    }

    [Fact]
    public void DependencyInspectionPreservesOverlappingOrdinalReferencesInPathOrder()
    {
        var manifest = Parse(
            Entry("Data/**/*.json", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"));
        const string input = "Data/input.json";
        string[] paths = [input, "Generated/é.json", "Generated/x/a.json", "Generated/a.json.long.json",
            "Generated/a.json", "Generated/E.json"];
        var findings = FileMapPolicy.InspectDependencies(manifest, paths,
            _ => "Generated/a.json.long.json Generated/x/a.json GENERATED/E.json Generated/é.json Generated/a.json Generated/a.json",
            new HashSet<string>([input], StringComparer.Ordinal));

        Assert.Equal(new[] { "Generated/a.json", "Generated/a.json.long.json", "Generated/x/a.json", "Generated/é.json" }
            .Select(path => new FileMapFinding("FILEMAP-DATA-GENERATED-DEPENDENCY", input,
                $"machine-readable data references generated artifact {path}")), findings);
    }

    [Fact]
    public void DeltaDependencyInspectionReadsOnlySelectedBodiesAndUsesCompleteGeneratedIndex()
    {
        var manifest = Parse(
            Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "LeanEmitter"),
            Entry("Main.lean", "truth", "none", "lake", "lean-build"));
        string[] paths = ["Data/changed.toml", "Data/untouched.toml", "Generated/output.json", "Main.lean"];
        var reads = new List<string>();
        var findings = FileMapPolicy.InspectDependencies(manifest, paths, path =>
        {
            reads.Add(path);
            return path == "Main.lean" ? "import Generated.Proof\n" : "projection = \"Generated/output.json\"\n";
        }, new HashSet<string>(["Data/changed.toml", "Main.lean"], StringComparer.Ordinal));

        Assert.Equal(new[] { "Data/changed.toml", "Main.lean" }, reads);
        Assert.Equal(new[] {
            new FileMapFinding("FILEMAP-DATA-GENERATED-DEPENDENCY", "Data/changed.toml", "machine-readable data references generated artifact Generated/output.json"),
            new FileMapFinding("FILEMAP-LEAN-GENERATED-IMPORT", "Main.lean", "Lean imports generated artifact Generated/Proof.lean"),
        }, findings);
    }

    [Fact]
    public void DeletedDependencyPathDoesNotReadUnchangedBodies()
    {
        var manifest = Parse(Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"));
        var reads = new List<string>();
        var findings = FileMapPolicy.InspectDependencies(manifest, ["Data/untouched.toml"], path =>
        {
            reads.Add(path);
            return "unchanged";
        }, new HashSet<string>(["Data/deleted.toml"], StringComparer.Ordinal));
        Assert.Empty(reads);
        Assert.Empty(findings);
    }

    [Fact]
    public void DependencyInspectionDoesNotRetainPreviouslyReadBodies()
    {
        var manifest = Parse(
            Entry("Data/**/*.json", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"));
        var paths = Enumerable.Range(0, 16).Select(index => $"Data/{index:D2}.json")
            .Append("Generated/result.json").ToArray();
        var bodies = new List<WeakReference<string>>();
        var maximumRetainedBodies = 0;
        var reads = new List<string>();

        var findings = FileMapPolicy.InspectDependencies(manifest, paths, path =>
        {
            GC.Collect();
            maximumRetainedBodies = Math.Max(maximumRetainedBodies,
                bodies.Count(reference => reference.TryGetTarget(out _)));
            reads.Add(path);
            var body = new string(' ', 1024 * 1024) + "Generated/result.json";
            bodies.Add(new WeakReference<string>(body));
            return body;
        });

        Assert.Equal(paths, reads);
        Assert.Equal(16, findings.Count);
        Assert.All(findings, finding => Assert.Equal("FILEMAP-DATA-GENERATED-DEPENDENCY", finding.Code));
        Assert.InRange(maximumRetainedBodies, 0, 2);
    }

    [Fact]
    public void DependencyInspectionPreservesAllFindingsAndReadsEachBodyOnce()
    {
        var manifest = Parse(
            Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "LeanEmitter"),
            Entry("Main.lean", "truth", "none", "lake", "lean-build"));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Main.lean"] = "import Generated.Proof\n",
            ["Generated/Proof.lean"] = "def generated : Nat := 0\n",
            ["Data/input.toml"] = "projection = \"Generated/output.json\"\n",
            ["Generated/output.json"] = "{}\n",
        };
        var reads = new List<string>();

        var findings = FileMapPolicy.InspectDependencies(manifest, files.Keys, path =>
        {
            reads.Add(path);
            return files[path];
        });

        FileMapFinding[] expected = [
            new("FILEMAP-DATA-GENERATED-DEPENDENCY", "Data/input.toml",
                "machine-readable data references generated artifact Generated/output.json"),
            new("FILEMAP-LEAN-GENERATED-IMPORT", "Main.lean",
                "Lean imports generated artifact Generated/Proof.lean"),
        ];
        Assert.Equal(expected, findings);
        Assert.Equal(expected, FileMapPolicy.InspectDependencies(manifest, files));
        Assert.Equal(new[] { "Data/input.toml", "Generated/Proof.lean", "Generated/output.json", "Main.lean" }, reads);
    }

    [Fact]
    public void DependencyInspectionStillReadsDataWhenNoGeneratedPathExists()
    {
        var manifest = Parse(Entry("Data/**/*.json", "data", "none", "loader", "SnapshotDecoder"));

        var exception = Assert.Throws<IOException>(() => FileMapPolicy.InspectDependencies(
            manifest, ["Data/unreadable.json"], _ => throw new IOException("unreadable input")));

        Assert.Equal("unreadable input", exception.Message);
    }
}
