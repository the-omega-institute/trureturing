using System.Text.Json.Nodes;


namespace StrataLint.FileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    private const string EngineeringManifest = "Meta/engineering-projects.json";
    private const string GeneratedInput = "Generated/output.json";

    [Theory]
    [InlineData("projects", true)]
    [InlineData("historical_projects", true)]
    [InlineData("projects", false)]
    [InlineData("historical_projects", false)]
    public void EngineeringPolicyQueriesDoNotReadGeneratedContent(string collection, bool targetExists)
    {
        Assert.Empty(InspectEngineeringDependencies(EngineeringQuery(collection).ToJsonString(), targetExists));
    }

    [Theory]
    [InlineData("projects", "execution_inputs", false)]
    [InlineData("projects", "execution_inputs", true)]
    [InlineData("historical_projects", "execution_inputs", true)]
    [InlineData("projects", "build_inputs", false)]
    [InlineData("projects", "build_inputs", true)]
    [InlineData("historical_projects", "build_inputs", true)]
    [InlineData("projects", "exclude", true)]
    [InlineData("projects", "namespace_exclude", true)]
    [InlineData("projects", "global_namespace_exceptions", true)]
    public void EngineeringContentReferencesRemainDependenciesAlongsideQueries(string collection, string field, bool query)
    {
        var generated = field is "exclude" or "namespace_exclude" or "global_namespace_exceptions"
            ? "Generated/Fixture.cs" : GeneratedInput;
        var document = EngineeringQuery(collection, generated);
        var project = document[collection]![0]!;
        if (!query) project["execution_filemap_paths"] = new JsonArray();
        project[field]!.AsArray().Add(generated);

        var finding = Assert.Single(InspectEngineeringDependencies(document.ToJsonString(), generatedInput: generated));
        Assert.Equal(new FileMapFinding("FILEMAP-DATA-GENERATED-DEPENDENCY", EngineeringManifest,
            $"machine-readable data references generated artifact {generated}"), finding);
    }

    [Theory]
    [InlineData("rule_build_inputs")]
    [InlineData("test_partition")]
    public void EngineeringQueriesDoNotHideOtherStringReferences(string field)
    {
        var document = EngineeringQuery("projects");
        if (field == "rule_build_inputs") document[field]!.AsArray().Add(GeneratedInput);
        else document["projects"]![0]![field] = GeneratedInput;
        Assert.Single(InspectEngineeringDependencies(document.ToJsonString()));
    }

    [Fact]
    public void EngineeringQuerySemanticsRequireTheCanonicalManifestPath()
    {
        var findings = InspectEngineeringDependencies(EngineeringQuery("projects").ToJsonString(),
            manifestPath: "Meta/other-projects.json");
        Assert.Equal("FILEMAP-DATA-GENERATED-DEPENDENCY", Assert.Single(findings).Code);
    }

    [Theory]
    [InlineData("projects", "unknown-field")]
    [InlineData("historical_projects", "unknown-field")]
    [InlineData("projects", "duplicate-key")]
    [InlineData("historical_projects", "duplicate-key")]
    [InlineData("projects", "invalid-role")]
    [InlineData("projects", "non-test-role")]
    [InlineData("historical_projects", "non-test-role")]
    [InlineData("projects", "wrong-type")]
    [InlineData("historical_projects", "wrong-type")]
    [InlineData("projects", "missing-filemap")]
    [InlineData("historical_projects", "missing-filemap")]
    [InlineData("projects", "excluded-filemap")]
    [InlineData("projects", "misplaced-query")]
    public void InvalidEngineeringSchemaCannotAcquireQuerySemantics(string collection, string defect)
    {
        var document = EngineeringQuery(collection);
        var project = document[collection]![0]!;
        switch (defect)
        {
            case "unknown-field": project["unknown"] = GeneratedInput; break;
            case "invalid-role": project["role"] = "unknown"; break;
            case "non-test-role":
                project["role"] = "test-support";
                project["ci"] = false;
                project["test_partition"] = null;
                break;
            case "wrong-type": project["execution_filemap_paths"] = GeneratedInput; break;
            case "missing-filemap": project["execution_inputs"] = new JsonArray(); break;
            case "excluded-filemap": project["execution_excludes"] = new JsonArray("Meta/**"); break;
            case "misplaced-query": document["execution_filemap_paths"] = new JsonArray(GeneratedInput); break;
        }
        var text = document.ToJsonString();
        if (defect == "duplicate-key") text = text.Replace("\"version\":1", "\"version\":1,\"version\":1", StringComparison.Ordinal);
        // Schema rejection also applies when the queried target has no physical body.
        Assert.Throws<InvalidDataException>(() => InspectEngineeringDependencies(text, targetExists: false));
    }

    private static JsonNode EngineeringQuery(string collection, string generatedInput = GeneratedInput)
    {
        var document = JsonNode.Parse($$"""
            {"version":1,"rule_build_inputs":[],"projects":[{
              "path":"tools/tests/Query/Query.csproj","assembly":"Query.Tests",
              "role":"cross-cutting-test","ci":true,"include":[],"exclude":[],
              "references":[],"owner":null,"owned_test_assembly":null,
              "test_partition":"query","root_namespace":"Query",
              "namespace_exclude":[],"global_namespace_exceptions":[],"build_inputs":[],
              "execution_inputs":["Meta/FILEMAP.toml"],"execution_excludes":[],
              "execution_environment":[],"execution_filemap_paths":["{{generatedInput}}"]
            }],"historical_projects":[]}
            """)!;
        if (collection == "historical_projects")
        {
            document[collection] = document["projects"]!.DeepClone();
            document["projects"] = new JsonArray();
        }
        return document;
    }

    private static IReadOnlyList<FileMapFinding> InspectEngineeringDependencies(string source,
        bool targetExists = true, string manifestPath = EngineeringManifest, string generatedInput = GeneratedInput)
    {
        var manifest = Parse(
            Entry(generatedInput, "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry(manifestPath, "data", "none", "loader", "EngineeringProjectRegistry"));
        string[] paths = targetExists ? [manifestPath, generatedInput] : [manifestPath];
        var reads = new List<string>();
        try
        {
            return FileMapPolicy.InspectDependencies(manifest, paths, path =>
            {
                reads.Add(path);
                Assert.Equal(manifestPath, path);
                return source;
            }, new HashSet<string>([manifestPath], StringComparer.Ordinal));
        }
        finally { Assert.Equal(new[] { manifestPath }, reads); }
    }

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
