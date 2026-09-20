using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
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
