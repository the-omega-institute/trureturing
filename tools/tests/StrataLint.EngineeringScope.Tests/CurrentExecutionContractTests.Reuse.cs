using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("source", 1)]
    [InlineData("reference", 2)]
    [InlineData("material", 1)]
    [InlineData("added-material", 1)]
    [InlineData("deleted-material", 1)]
    [InlineData("mode", 1)]
    [InlineData("build-option", 1)]
    [InlineData("unrelated-row", 0)]
    public void RegisteredInputChangesSelectOnlyTheirReferenceClosure(string change, int selected)
    {
        using var fixture = new CandidateFixture();
        fixture.Write("tools/tests/First/Input.cs", "// first\n");
        fixture.Write("fixtures/input.txt", "first\n");
        fixture.Write("options.txt", "release\n");
        EditRegistration(fixture, rows =>
        {
            rows[0]!["execution_inputs"] = new JsonArray("fixtures/*.txt");
            rows[0]!["build_inputs"] = new JsonArray("options.txt");
            if (change == "reference") rows[1]!["references"] = new JsonArray(CandidateFixture.First);
        });
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        switch (change)
        {
            case "source": case "reference": fixture.Write("tools/tests/First/Input.cs", "// changed\n"); break;
            case "material": fixture.Write("fixtures/input.txt", "changed\n"); break;
            case "added-material": fixture.Write("fixtures/added.txt", "new\n"); break;
            case "deleted-material": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, "fixtures/input.txt")); break;
            case "mode":
                if (OperatingSystem.IsWindows()) return;
                File.SetUnixFileMode(Path.Combine(fixture.Root, "fixtures/input.txt"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
                break;
            case "build-option": fixture.Write("options.txt", "changed\n"); break;
            case "unrelated-row":
                fixture.Write("tools/support/Support.csproj", "<Project />\n");
                var path = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
                TemporaryFileSystem.File.WriteAllText(path, EngineeringRegistrationFixture.Append(
                    TemporaryFileSystem.File.ReadAllText(path), new EngineeringProjectFixture("tools/support/Support.csproj", "Support", "test-support", false, [])));
                break;
        }
        fixture.Track();
        Assert.Equal(selected, Execute(fixture).Count);
    }

    [Theory]
    [InlineData("missing-inputs")]
    [InlineData("missing-excludes")]
    [InlineData("missing-file")]
    [InlineData("conflicting-input")]
    [InlineData("duplicate-input")]
    [InlineData("reference")]
    [InlineData("cycle")]
    [InlineData("unregistered")]
    public void InvalidCurrentRegistrationFailsBeforeAnyRunnerCall(string defect)
    {
        using var fixture = new CandidateFixture();
        EditRegistration(fixture, rows =>
        {
            var row = rows[0]!;
            switch (defect)
            {
                case "missing-inputs": row.AsObject().Remove("execution_inputs"); break;
                case "missing-excludes": row.AsObject().Remove("execution_excludes"); break;
                case "missing-file": row["execution_inputs"] = new JsonArray("absent.json"); break;
                case "conflicting-input": row["execution_inputs"] = new JsonArray("needed.json"); row["execution_excludes"] = new JsonArray("needed.json"); break;
                case "duplicate-input": row["execution_inputs"] = new JsonArray("fixtures/**", "fixtures/**"); break;
                case "reference": row["references"] = new JsonArray("tools/missing.csproj"); break;
                case "cycle": row["references"] = new JsonArray(CandidateFixture.Second); rows[1]!["references"] = new JsonArray(CandidateFixture.First); break;
            }
        });
        if (defect == "unregistered") fixture.Write("tools/unregistered.csproj", "<Project />");
        fixture.Track();
        var calls = 0;
        Assert.ThrowsAny<Exception>(() => Program.RunCurrentTests(fixture.Root, (_, _) => { ++calls; return 0; }, TextWriter.Null));
        Assert.Equal(0, calls);
    }

    [Theory]
    [InlineData("deleted")]
    [InlineData("disabled")]
    [InlineData("missing-row")]
    [InlineData("failed-row")]
    public void BaseRegisteredProjectStillRequiresCurrentAcceptedSuccess(string defect)
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        Seed(fixture);
        if (defect is "deleted" or "disabled")
        {
            EditRegistration(fixture, rows =>
            {
                if (defect == "deleted") rows.RemoveAt(0);
                else rows[0]!["ci"] = false;
            });
            if (defect == "deleted") TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CandidateFixture.First));
            fixture.Track();
            Execute(fixture);
        }
        else
        {
            var record = ReadTests(fixture);
            if (defect == "missing-row") record["projects"]!.AsArray().RemoveAt(0);
            else record["projects"]![0]!["exit"] = 1;
            TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath), record.ToJsonString());
        }
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root, [CandidateFixture.First]));
    }

    [Theory]
    [InlineData("nonzero")]
    [InlineData("malformed")]
    [InlineData("zero")]
    [InlineData("wrong-assembly")]
    [InlineData("infrastructure")]
    public void SelectedFailureNeverRetriesOrFallsBackToOldSuccess(string failure)
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        Seed(fixture);
        fixture.Write("tools/tests/First/Input.cs", "// select first\n");
        fixture.Track();
        fixture.Build();
        var calls = 0;
        Assert.Equal(1, Program.RunCurrentTests(fixture.Root, (_, directory) =>
        {
            ++calls;
            fixture.WriteTrx(directory, failure == "zero" ? "NotExecuted" : "Passed");
            var path = Path.Combine(directory, "execution.trx");
            if (failure == "malformed") TemporaryFileSystem.File.WriteAllText(path, "broken XML");
            if (failure == "wrong-assembly") TemporaryFileSystem.File.WriteAllText(path, TemporaryFileSystem.File.ReadAllText(path).Replace("First.dll", "Wrong.dll", StringComparison.Ordinal));
            if (failure == "infrastructure") TemporaryFileSystem.File.WriteAllText(path,
                File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "Fixtures/infrastructure-skip.trx")));
            return failure == "nonzero" ? 1 : 0;
        }, TextWriter.Null));
        Assert.Equal(1, calls);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    private static void EditRegistration(CandidateFixture fixture, Action<JsonArray> edit)
    {
        var path = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
        var registration = JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!;
        edit(registration["projects"]!.AsArray());
        TemporaryFileSystem.File.WriteAllText(path, registration.ToJsonString());
    }

    [Fact]
    public void EqualRegisteredInputsAcrossCandidatesReuseOriginalExecutionRepeatedly()
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        var original = ReadTests(fixture);
        for (var round = 0; round != 2; ++round)
        {
            Seed(fixture);
            TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, ".gitignore"), "# unrelated\n");
            var calls = Execute(fixture);
            Assert.Empty(calls);
            var current = ReadTests(fixture);
            Assert.NotEqual(original["candidate"]!.ToString(), current["candidate"]!.ToString());
            foreach (var row in current["projects"]!.AsArray())
            {
                var prior = original["projects"]!.AsArray().Single(item => item!["project"]!.ToString() == row!["project"]!.ToString())!;
                Assert.Equal("reused", row!["status"]!.ToString());
                foreach (var field in new[] { "results", "execution_candidate", "execution_round", "input_fingerprint" })
                    Assert.Equal(prior[field]!.ToString(), row[field]!.ToString());
            }
            CommonExecutionEvidence.ValidateTests(fixture.Root, [CandidateFixture.First]);
        }
    }

    [Theory]
    [InlineData("absent", 2)]
    [InlineData("json", 2)]
    [InlineData("partial", 1)]
    [InlineData("material", 1)]
    [InlineData("missing-trx", 1)]
    [InlineData("origin", 1)]
    [InlineData("fingerprint", 1)]
    [InlineData("wrong-assembly", 1)]
    [InlineData("malformed-row", 1)]
    public void OptionalSeedExecutesOnlyUnavailableProjects(string defect, int count)
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        if (defect != "absent") Seed(fixture);
        const string seed = "build/ci/test-seed";
        if (defect == "json") TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, seed, "tests.json"), "broken");
        else if (defect != "absent")
        {
            var record = ReadTests(fixture);
            var first = record["projects"]![0]!;
            if (defect == "partial") record["projects"]!.AsArray().RemoveAt(0);
            if (defect == "malformed-row") first.AsObject().Remove("exit");
            if (defect == "origin") first["execution_round"] = "wrong-origin";
            if (defect == "fingerprint") first["input_fingerprint"] = new string('0', 64);
            if (defect is "material" or "missing-trx" or "wrong-assembly")
            {
                var material = record["materials"]!.AsArray().First(item => item!["path"]!.ToString().StartsWith(first["results"]!.ToString() + "/", StringComparison.Ordinal))!;
                var file = Path.Combine(fixture.Root, seed, material["path"]!.ToString());
                if (defect == "material") TemporaryFileSystem.File.AppendAllText(file, "corrupt");
                else if (defect == "missing-trx") TemporaryFileSystem.File.Delete(file);
                else
                {
                    TemporaryFileSystem.File.WriteAllText(file, TemporaryFileSystem.File.ReadAllText(file).Replace("First.dll", "Wrong.dll", StringComparison.Ordinal));
                    material["sha256"] = CommonExecutionEvidence.Hash(file);
                }
            }
            TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, seed, "tests.json"), record.ToJsonString());
        }
        Assert.Equal(count, Execute(fixture).Count);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("material")]
    [InlineData("origin")]
    [InlineData("status")]
    public void CurrentAcceptanceTamperingFailsHard(string field)
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        Seed(fixture);
        Execute(fixture);
        var record = ReadTests(fixture);
        if (field is "candidate" or "round") record[field] = "wrong";
        else if (field == "origin") record["projects"]![0]!["execution_round"] = "wrong";
        else if (field == "status") record["projects"]![0]!["status"] = "executed";
        else TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, record["materials"]![0]!["path"]!.ToString()), "corrupt");
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath), record.ToJsonString());
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Fact]
    public void SeedExportRequiresEngineeringAcceptanceAndSaveFailurePreservesResult()
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ExportTestSeed(fixture.Root, TextWriter.Null));
        AcceptEngineering(fixture);
        fixture.Write("build/blocked", "file blocks a seed directory");
        using var output = new StringWriter();
        Assert.False(CommonExecutionEvidence.ExportTestSeed(fixture.Root, output, Path.Combine(fixture.Root, "build/blocked/seed")));
        Assert.Contains("ENGINEERING_TEST_SEED_NOT_SAVED", output.ToString(), StringComparison.Ordinal);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
        Assert.True(CommonExecutionEvidence.ExportTestSeed(fixture.Root, output));
    }

    [Fact]
    public void ExportedSeedTransfersAcrossRootsAndKeepsOriginalTrxThroughRepeatedExport()
    {
        using var source = new CandidateFixture();
        using var target = new CandidateFixture();
        Execute(source);
        AcceptEngineering(source);
        var original = CommonExecutionEvidence.ValidateTests(source.Root);
        Assert.True(CommonExecutionEvidence.ExportTestSeed(source.Root, TextWriter.Null, Path.Combine(target.Root, CommonExecutionEvidence.TestSeedPath)));
        for (var round = 0; round < 2; ++round)
        {
            target.Write("notes.txt", "candidate " + round);
            target.Track();
            Assert.Empty(Execute(target));
            AcceptEngineering(target);
            Assert.True(CommonExecutionEvidence.ExportTestSeed(target.Root, TextWriter.Null));
            var accepted = CommonExecutionEvidence.ValidateTests(target.Root);
            Assert.Equal(original.Materials, accepted.Materials);
            Assert.Equal(original.Projects.Select(row => row with { Status = "reused" }), accepted.Projects);
        }
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("inventory")]
    [InlineData("assembly")]
    [InlineData("material")]
    public void InvalidCurrentBuildFailsBeforeAnySelection(string defect)
    {
        using var fixture = new CandidateFixture();
        Execute(fixture);
        Seed(fixture);
        if (defect == "missing") TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath));
        else if (defect == "material") fixture.Write("build/ci/fixture-bin/First.dll", "changed");
        else
        {
            var inventory = CommonExecutionEvidence.Read<BuiltTestProject[]>(fixture.Root, CommonBuildOutputs.TestsPath);
            CommonExecutionEvidence.Write(fixture.Root, CommonBuildOutputs.TestsPath,
                defect == "inventory" ? inventory.Skip(1).ToArray() : inventory.Select(row => row with { Assembly = "build/ci/fixture-bin/Second.dll" }).ToArray());
            var build = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.BuildPath);
            CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.BuildPath,
                build with { Materials = CommonExecutionEvidence.Materials(fixture.Root, build.Materials.Select(row => row.Path)) });
        }
        var calls = 0;
        Assert.ThrowsAny<Exception>(() => Program.RunCurrentTests(fixture.Root, (_, _) => { ++calls; return 0; }, TextWriter.Null));
        Assert.Equal(0, calls);
    }

    [Fact]
    public void ManifestRuntimeInputsProjectOnlyRelevantRows()
    {
        using var fixture = new CandidateFixture();
        fixture.Write("fixtures/input.txt", "material");
        const string filemap = "[[files]]\npattern = \"fixtures/*.txt\"\nkind = \"data\"\nadmission_plane = \"judge\"\n";
        fixture.Write("Meta/FILEMAP.toml", filemap);
        EditRegistration(fixture, rows => rows[0]!["execution_inputs"] = new JsonArray(
            "fixtures/*.txt", "Meta/FILEMAP.toml", EngineeringRegistrationFixture.Path));
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        fixture.Write("Meta/FILEMAP.toml", filemap + "[[files]]\npattern = \"unrelated/**\"\nkind = \"data\"\n");
        Assert.Empty(Execute(fixture));
        Seed(fixture);
        fixture.Write("Meta/FILEMAP.toml", filemap.Replace("data", "projection", StringComparison.Ordinal));
        Assert.Equal([CandidateFixture.First], Execute(fixture));
    }

    private static void AcceptEngineering(CandidateFixture fixture)
    {
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        CommonExecutionEvidence.SealEngineering(fixture.Root, build, CommonExecutionEvidence.EngineeringSteps.Select(name =>
            new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", "build/ci/fixture-build.log")).ToArray());
    }

    private static List<string> Execute(CandidateFixture fixture)
    {
        fixture.Build();
        var calls = new List<string>();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        return calls;
    }

    private static JsonNode ReadTests(CandidateFixture fixture) => JsonNode.Parse(
        TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)))!;

    private static void Seed(CandidateFixture fixture)
    {
        var record = ReadTests(fixture);
        var seed = Path.Combine(fixture.Root, "build/ci/test-seed");
        TemporaryFileSystem.Directory.CreateDirectory(seed);
        foreach (var material in record["materials"]!.AsArray())
        {
            var path = material!["path"]!.ToString();
            var target = Path.Combine(seed, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            TemporaryFileSystem.File.WriteAllBytes(target, TemporaryFileSystem.File.ReadAllBytes(Path.Combine(fixture.Root, path)));
        }
        TemporaryFileSystem.File.WriteAllText(Path.Combine(seed, "tests.json"), record.ToJsonString());
    }
}
