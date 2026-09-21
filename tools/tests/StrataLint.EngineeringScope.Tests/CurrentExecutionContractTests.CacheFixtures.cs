using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("Meta/FILEMAP.toml", true)]
    [InlineData("Meta/FILEMAP.fixture.toml", true)]
    [InlineData("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json", true)]
    [InlineData("README.md", false)]
    [InlineData("policy:README.md", true)]
    [InlineData("policy:docs/develop/theory/**", true)]
    [InlineData("policy:unrelated/**", false)]
    [InlineData("source-policy:README.md", true)]
    [InlineData("source-policy:docs/develop/theory/**", true)]
    [InlineData("source-policy:agents/**", false)]
    [InlineData("source-policy:Meta/Digestion/atoms/sha256/*", true)]
    [InlineData("declaration", true)]
    public void RegisteredScribeFileMapInputsInvalidateEvidenceWhileUnrelatedDocumentationReusesIt(string path, bool invalidates)
    {
        using var fixture = new CandidateFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj")!;
        // Use Scribe's actual runtime registration with the small fixture's compile inputs.
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_filemap_paths" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            fixture.Write(input, "registered fixture material\n");
        var filemap = """
            schema_version = 4
            resources = [{ id = "lean-report", cache_layers = [], cache_activation = {} }]
            [[files]]
            pattern = "README.md"
            kind = "reference"
            require = []
            [[files]]
            pattern = "docs/develop/theory/**"
            kind = "reference"
            require = []
            [[files]]
            pattern = "unrelated/**"
            kind = "reference"
            require = []
            """ + "\n";
        if (path.StartsWith("source-policy:", StringComparison.Ordinal))
        {
            filemap = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/FILEMAP.toml"));
            fixture.Write("Meta/FILEMAP.docs.reports.toml", TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("Meta/FILEMAP.docs.reports.toml")));
        }
        fixture.Write("Meta/FILEMAP.toml", filemap);
        // Keep the fragment independent of root includes to exercise its explicit glob.
        fixture.Write("Meta/FILEMAP.fixture.toml", """
            schema_version = 4
            [[files]]
            pattern = "docs/reports/**"
            kind = "reference"
            require = []
            """ + "\n");
        fixture.Write("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json", "{\"cases\":[]}\n");
        fixture.Write("README.md", "original documentation\n");
        Assert.False(File.Exists(Path.Combine(fixture.Root, "docs/develop/theory/input.md")));
        fixture.Track();
        Assert.Equal([CandidateFixture.First, CandidateFixture.Second], Execute(fixture));
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);

        if (path == "declaration")
            EditRegistration(fixture, rows => rows[0]!["execution_filemap_paths"]!.AsArray().RemoveAt(0));
        else if (path.StartsWith("source-policy:", StringComparison.Ordinal))
        {
            var row = Assert.Single(filemap.Split('\n'), line => line.Contains($"pattern = \"{path[14..]}\"", StringComparison.Ordinal));
            var changed = row.Replace("require = []", "require = [\"filemap\"]", StringComparison.Ordinal)
                .Replace("require = [\"delta\", \"engineering\", \"filemap\"]", "require = [\"filemap\"]", StringComparison.Ordinal)
                .Replace("kind = \"ledger\"", "kind = \"data\"", StringComparison.Ordinal);
            Assert.NotEqual(row, changed);
            fixture.Write("Meta/FILEMAP.toml", filemap.Replace(row, changed, StringComparison.Ordinal));
        }
        else if (path.StartsWith("policy:", StringComparison.Ordinal))
            fixture.Write("Meta/FILEMAP.toml", filemap.Replace(
                $"pattern = \"{path[7..]}\"\nkind = \"reference\"\nrequire = []",
                $"pattern = \"{path[7..]}\"\nkind = \"reference\"\nrequire = [\"filemap\"]", StringComparison.Ordinal));
        else if (path == "Meta/FILEMAP.toml")
            fixture.Write(path, filemap.Replace("cache_layers = [], cache_activation = {}",
                "cache_layers = [\"current\"], cache_activation = { current = \"stage-start\" }", StringComparison.Ordinal));
        else File.AppendAllText(Path.Combine(fixture.Root, path), "\n");
        fixture.Track();

        Assert.Equal(invalidates ? new[] { CandidateFixture.First } : [], Execute(fixture));
        var accepted = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.NotEqual(prior.Candidate, accepted.Candidate);
        if (invalidates)
        {
            Assert.NotEqual(prior.Projects[0].InputFingerprint, accepted.Projects[0].InputFingerprint);
            Assert.Equal("executed", accepted.Projects[0].Status);
        }
        else Assert.Equal(prior.Projects[0] with { Status = "reused" }, accepted.Projects[0]);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, accepted.Projects[1]);
        AcceptEngineering(fixture);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
        if (invalidates)
        {
            // Even with current candidate/build provenance, old successful TRX cannot
            // pass final acceptance after a consumed input changes.
            CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, accepted with
            {
                Projects = prior.Projects.Select(project => project with { Status = "reused" }).ToArray(),
                Materials = prior.Materials,
            });
            Assert.Contains("test input identity mismatch", Assert.Throws<InvalidDataException>(() =>
                CommonExecutionEvidence.ValidateEngineering(fixture.Root)).Message);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FileMapQueryRequiresRuntimeMaterialIncludingDisabledProjects(bool enabled)
    {
        using var fixture = new CandidateFixture();
        EditRegistration(fixture, rows =>
        {
            rows[1]!["ci"] = enabled;
            rows[1]!["execution_inputs"] = new JsonArray("Meta/**");
            rows[1]!["execution_filemap_paths"] = new JsonArray("docs/virtual.md");
        });
        fixture.Build();
        var calls = 0;
        var error = Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root,
            (_, _) => { ++calls; return 0; }, TextWriter.Null));
        Assert.Equal(0, calls);
        Assert.Contains("FILEMAP runtime input is absent", error.Message);
        Assert.Contains(CandidateFixture.Second, error.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FileMapQueryDeclarationsBindRuntimeReadersWithoutChangingCompileInputs(bool readsRegistration)
    {
        using var fixture = new CandidateFixture();
        fixture.Write("Meta/FILEMAP.toml", "[[files]]\npattern = \"README.md\"\nrequire = []\n");
        EditRegistration(fixture, rows =>
        {
            rows[0]!["execution_inputs"] = new JsonArray("Meta/FILEMAP.toml");
            rows[1]!["references"] = new JsonArray(CandidateFixture.First);
            if (readsRegistration) rows[1]!["execution_inputs"] = new JsonArray(EngineeringRegistrationFixture.Path);
        });
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        // No FILEMAP row or file bytes change. This unmatched virtual query tests
        // the declaration's own identity, including relevant manifest projections.
        EditRegistration(fixture, rows => rows[0]!["execution_filemap_paths"] = new JsonArray("docs/virtual.md"));
        Assert.Equal(readsRegistration ? [CandidateFixture.First, CandidateFixture.Second] : new[] { CandidateFixture.First }, Execute(fixture));
        CommonExecutionEvidence.ValidateTests(fixture.Root);
    }

    [Theory]
    [InlineData("D5/S0/CacheInputProbe.lean", false)]
    [InlineData("Blueprint/CacheInputProbe.scribe.cs", false)]
    [InlineData("Meta/Digestion/backfill/cache-input-probe.json", false)]
    [InlineData("tools/scripts/worktree/lean_actions.py", true)]
    [InlineData("tools/scripts/worktree/lean_cache_release.py", true)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py", true)]
    public void RegisteredCacheFixtureInputsReuseContentChangesAndRerunCacheChanges(string path, bool invalidates)
    {
        using var fixture = new CandidateFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        const string documents = "tools/fixture/BlueprintFixture.csproj";
        fixture.Write(documents, "<Project />\n");
        var manifest = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
        File.WriteAllText(manifest, EngineeringRegistrationFixture.Append(File.ReadAllText(manifest),
            new EngineeringProjectFixture(documents, "BlueprintFixture", "test-support", false, ["Blueprint/**/*.scribe.cs"])));
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            if (!File.Exists(Path.Combine(fixture.Root, input))) fixture.Write(input, input == "Meta/FILEMAP.toml"
                ? "schema_version = 4\n[[files]]\npattern = \"tools/tests/First/**\"\nkind = \"program\"\n"
                : "registered fixture material\n");
        fixture.Write(path, "original registered input\n");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];

        fixture.Write(path, "changed registered input\n");
        fixture.Track();

        var calls = Execute(fixture);
        Assert.True(calls.SequenceEqual(invalidates ? new[] { CandidateFixture.First } : []),
            $"[FAIL] cache_fixture_input_isolation: {path}: invalidates={invalidates}; executed={string.Join(',', calls)}");
        var accepted = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];
        if (invalidates) Assert.NotEqual(prior.InputFingerprint, accepted.InputFingerprint);
        else Assert.Equal(prior with { Status = "reused" }, accepted);
    }
}
