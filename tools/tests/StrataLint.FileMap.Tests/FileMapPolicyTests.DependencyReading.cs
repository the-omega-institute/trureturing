using System.Text.Json.Nodes;


namespace StrataLint.FileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    private const string EngineeringManifest = "Meta/engineering-projects.json";
    private const string GeneratedInput = "Generated/output.json";

    [Fact]
    public void CiSelectionPatternsDoNotCreateContentDependencies()
    {
        var document = CiSelection();
        document["shared_inputs"]!.AsArray().Add(GeneratedInput);
        document["units"]![0]!["inputs"]!.AsArray().Add(GeneratedInput);
        Assert.Empty(InspectCiDependencies(document.ToJsonString()));
    }

    [Theory]
    [InlineData("workflow")]
    [InlineData("project")]
    public void CiContentReferencesRemainDependencies(string field)
    {
        var document = CiSelection();
        document["units"]![0]![field] = GeneratedInput;
        Assert.Single(InspectCiDependencies(document.ToJsonString()));
    }

    [Fact]
    public void CiCacheProjectRemainsDependency()
    {
        var document = CiSelection();
        document["caches"] = new JsonObject
        {
            ["judge"] = new JsonObject { ["project"] = GeneratedInput, ["inputs"] = new JsonArray() },
        };
        Assert.Single(InspectCiDependencies(document.ToJsonString()));
    }

    [Theory]
    [InlineData("schema")]
    [InlineData("shared-type")]
    [InlineData("closure-type")]
    [InlineData("caches-type")]
    [InlineData("cache-unknown-field")]
    [InlineData("input-type")]
    [InlineData("unknown-field")]
    [InlineData("duplicate-key")]
    public void InvalidCiSelectionShapeCannotHideContentReferences(string defect)
    {
        var document = CiSelection();
        switch (defect)
        {
            case "schema": document["schema"] = "unknown"; break;
            case "shared-type": document["shared_inputs"] = GeneratedInput; break;
            case "closure-type": document["closure_excludes"] = GeneratedInput; break;
            case "caches-type": document["caches"] = GeneratedInput; break;
            case "cache-unknown-field":
                document["caches"] = JsonNode.Parse("""{"judge":{"project":"p.csproj","inputs":[],"unknown":1}}""");
                break;
            case "input-type": document["units"]![0]!["inputs"] = GeneratedInput; break;
            case "unknown-field": document["units"]![0]!["unknown"] = GeneratedInput; break;
        }
        var text = document.ToJsonString();
        if (defect == "duplicate-key") text = text.Replace("\"schema\":", "\"schema\":\"ci-units-v1\",\"schema\":", StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => InspectCiDependencies(text));
    }

    private static JsonNode CiSelection() => JsonNode.Parse("""
        {"schema":"ci-units-v1","shared_inputs":[],"closure_excludes":[],"caches":{},"units":[{
          "id":"fixture","workflow":".github/workflows/ci-fixture.yml","project":null,
          "test":false,"lean":"none","dotnet":false,"inputs":[]
        }]}
        """)!;

    private static IReadOnlyList<FileMapFinding> InspectCiDependencies(string source)
    {
        const string input = "Meta/ci-units.json";
        var manifest = Parse(
            Entry(GeneratedInput, "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry(input, "data", "none", "GitHub-Actions", "CiUnits"));
        return FileMapPolicy.InspectDependencies(manifest, new Dictionary<string, string>
        {
            [input] = source,
            [GeneratedInput] = "{}",
        });
    }

    [Theory]
    [InlineData("projects", "include")]
    [InlineData("historical_projects", "include")]
    [InlineData("projects", "exclude")]
    [InlineData("projects", "namespace_exclude")]
    [InlineData("projects", "global_namespace_exceptions")]
    public void EngineeringContentReferencesRemainDependenciesAlongsideQueries(string collection, string field)
    {
        const string generated = "Generated/Fixture.cs";
        var document = EngineeringQuery(collection);
        document[collection]![0]![field]!.AsArray().Add(generated);
        Assert.Equal(new FileMapFinding("FILEMAP-DATA-GENERATED-DEPENDENCY", EngineeringManifest,
            $"machine-readable data references generated artifact {generated}"),
            Assert.Single(InspectEngineeringDependencies(document.ToJsonString(), generatedInput: generated)));
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

    [Theory]
    [InlineData("projects", "unknown-field")]
    [InlineData("historical_projects", "unknown-field")]
    [InlineData("projects", "duplicate-key")]
    [InlineData("historical_projects", "duplicate-key")]
    [InlineData("projects", "invalid-role")]
    [InlineData("historical_projects", "invalid-role")]
    [InlineData("projects", "wrong-type")]
    [InlineData("historical_projects", "wrong-type")]
    public void InvalidEngineeringSchemaCannotAcquireQuerySemantics(string collection, string defect)
    {
        var document = EngineeringQuery(collection);
        var project = document[collection]![0]!;
        switch (defect)
        {
            case "unknown-field": project["unknown"] = GeneratedInput; break;
            case "invalid-role": project["role"] = "unknown"; break;
            case "wrong-type": project["include"] = GeneratedInput; break;
        }
        var text = document.ToJsonString();
        if (defect == "duplicate-key") text = text.Replace("\"version\":1", "\"version\":1,\"version\":1", StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => InspectEngineeringDependencies(text));
        Assert.Throws<InvalidDataException>(() => InspectEngineeringDependencies(text, targetExists: false));
    }

    private static JsonNode EngineeringQuery(string collection)
    {
        var document = JsonNode.Parse($$"""
            {"version":1,"rule_build_inputs":[],"projects":[{
              "path":"tools/tests/Query/Query.csproj","assembly":"Query.Tests",
              "role":"cross-cutting-test","include":[],"exclude":[],
              "references":[],"owner":null,"owned_test_assembly":null,
              "test_partition":"query","root_namespace":"Query",
              "namespace_exclude":[],"global_namespace_exceptions":[]
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
        var manifest = Parse(new[] {
            Entry(generatedInput, "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry(manifestPath, "data", "none", "loader", "EngineeringProjectRegistry"),
        }.Order(StringComparer.Ordinal).ToArray());
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
