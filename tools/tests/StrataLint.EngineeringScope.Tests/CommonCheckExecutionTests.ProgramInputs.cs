using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CommonCheckExecutionTests
{
    private const string ProgramA = "tools/tests/First/A.cs";
    private const string ProgramB = "tools/tests/First/B.cs";
    private const string SharedProgram = "tools/tests/First/Shared.cs";

    [Theory]
    [InlineData(ProgramA, "SL-015")]
    [InlineData(ProgramB, "SL-019")]
    [InlineData(SharedProgram, "SL-015,SL-019")]
    [InlineData("tools/tests/First/Unrelated.cs", "")]
    public void DeclaredCheckProgramsIsolateInputsWithinOneAssembly(string changed, string expected)
    {
        using var fixture = new ReportInputsFixture();
        RegisterCheckPrograms(fixture);
        fixture.Tree.Write(changed, "class Original {}\n");
        fixture.Tree.Track();
        var original = fixture.Run();
        fixture.Seed();
        fixture.Tree.Write(changed, "class Changed {}\n");
        fixture.Tree.Track();

        var current = fixture.Run();

        Assert.Equal(expected.Split(',', StringSplitOptions.RemoveEmptyEntries), fixture.Calls);
        Assert.All(current.Units.Where(unit => !fixture.Calls.Contains(unit.Id)), unit =>
        {
            var previous = original.Units.Single(item => item.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(previous.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(previous.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(previous.Materials, unit.Materials);
        });
    }

    [Theory]
    [InlineData("tools/tests/Second/Consumer.cs", true)]
    [InlineData("tools/tests/Second/Unrelated.cs", false)]
    public void DeclaredConsumerProgramsIsolateInputsWithinOneAssembly(string changed, bool rerun)
    {
        using var fixture = new ReportInputsFixture();
        var consumer = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, ReportInputsFixture.LeanConsumer)))!;
        consumer["projects"] = new JsonArray(CurrentExecutionContractTests.CandidateFixture.Second);
        consumer["program_inputs"] = new JsonArray("tools/tests/Second/Consumer.cs");
        fixture.Tree.Write(ReportInputsFixture.LeanConsumer, consumer.ToJsonString());
        fixture.Tree.Write("tools/tests/Second/Consumer.cs", "class Consumer {}\n");
        fixture.Tree.Write(changed, "class Original {}\n");
        fixture.Tree.Track();
        fixture.Run();
        fixture.Seed();
        fixture.Tree.Write(changed, "class Changed {}\n");
        fixture.Tree.Track();

        fixture.Run();

        Assert.Equal(rerun ? ["SL-006"] : Array.Empty<string>(), fixture.Calls);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void MissingCheckOrConsumerProgramRegistrationFailsBeforeWork(bool consumer, bool missingFile)
    {
        using var fixture = new ReportInputsFixture();
        const string absent = "tools/tests/First/Absent.cs";
        if (consumer)
        {
            var path = ReportInputsFixture.LeanConsumer;
            var row = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, path)))!.AsObject();
            if (missingFile) row["program_inputs"] = new JsonArray(absent);
            else row.Remove("program_inputs");
            fixture.Tree.Write(path, row.ToJsonString());
        }
        else fixture.Edit(rows =>
        {
            var row = rows.Single(item => item!["id"]!.ToString() == "SL-015")!.AsObject();
            if (missingFile) row["program_inputs"] = new JsonArray(absent);
            else row.Remove("program_inputs");
        });
        fixture.Tree.Track();

        var error = Assert.Throws<InvalidDataException>(() => fixture.Run());

        Assert.Contains(missingFile ? absent : "program_inputs", error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Fact]
    public void ChangedCheckProgramFailureCannotReusePreviousSuccess()
    {
        using var fixture = new ReportInputsFixture();
        RegisterCheckPrograms(fixture);
        fixture.Run();
        fixture.Seed();
        fixture.Tree.Write(ProgramA, "class Invalidated {}\n");
        fixture.Tree.Track();
        var build = fixture.Tree.Build();
        var checks = CommonExecutionEvidence.BeginChecks(fixture.Root, "current", build, TextWriter.Null);
        var calls = 0;

        Assert.Throws<InvalidDataException>(() => checks.Run("SL-015", () =>
        {
            calls++;
            return new([new("SL-015", 1, "current program failed")]);
        }));

        Assert.Equal(1, calls);
        Assert.DoesNotContain(checks.Completed, unit => unit.Id == "SL-015");
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath("current"))));
    }

    [Theory]
    [InlineData("add")]
    [InlineData("delete")]
    [InlineData("mode")]
    public void CheckProgramMembershipAndModeChangesInvalidateTheirOwner(string change)
    {
        if (change == "mode" && OperatingSystem.IsWindows()) return;
        using var fixture = new ReportInputsFixture();
        RegisterCheckPrograms(fixture);
        const string path = "tools/tests/First/Growth/Member.cs";
        fixture.Edit(rows => rows.Single(row => row!["id"]!.ToString() == "SL-015")!["program_inputs"] =
            new JsonArray(ProgramA, SharedProgram, "tools/tests/First/Growth/*.cs"));
        if (change != "add") fixture.Tree.Write(path, "class Member {}\n");
        fixture.Tree.Track();
        fixture.Run();
        fixture.Seed();
        if (change == "delete") File.Delete(Path.Combine(fixture.Root, path));
        else if (change == "add") fixture.Tree.Write(path, "class Member {}\n");
        else File.SetUnixFileMode(Path.Combine(fixture.Root, path), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        fixture.Tree.Track();

        fixture.Run();

        Assert.Equal(new[] { "SL-015" }, fixture.Calls);
    }

    [Theory]
    [InlineData(false, "empty")]
    [InlineData(false, "duplicate")]
    [InlineData(false, "outside")]
    [InlineData(true, "empty")]
    [InlineData(true, "duplicate")]
    [InlineData(true, "outside")]
    public void InvalidProgramInputRegistrationNamesItsOwnerBeforeWork(bool consumer, string defect)
    {
        using var fixture = new ReportInputsFixture();
        var inputs = defect switch
        {
            "empty" => new JsonArray(),
            "duplicate" => new JsonArray("global.json", "global.json"),
            _ => new JsonArray("../outside.cs"),
        };
        if (consumer)
        {
            var row = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, ReportInputsFixture.LeanConsumer)))!;
            row["program_inputs"] = inputs;
            fixture.Tree.Write(ReportInputsFixture.LeanConsumer, row.ToJsonString());
        }
        else fixture.Edit(rows => rows.Single(row => row!["id"]!.ToString() == "SL-015")!["program_inputs"] = inputs);
        fixture.Tree.Track();

        var error = Assert.Throws<InvalidDataException>(() => fixture.Run());

        Assert.Contains(consumer ? ReportInputsFixture.LeanConsumer : "SL-015", error.Message, StringComparison.Ordinal);
        Assert.Contains("program_inputs", error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Theory]
    [InlineData("reference-source", 0)]
    [InlineData("reference-project", 22)]
    [InlineData("build-config", 22)]
    public void ProgramInputNarrowingRetainsRegisteredProjectAndBuildIdentity(string changed, int expected)
    {
        using var fixture = new ReportInputsFixture();
        RegisterCheckPrograms(fixture);
        const string referenceSource = "tools/tests/Second/Reference.cs";
        const string configuration = "fixtures/compiler-options.txt";
        fixture.Tree.Write(referenceSource, "class Reference {}\n");
        fixture.Tree.Write(configuration, "original options\n");
        var manifestPath = Path.Combine(fixture.Root, "Meta/engineering-projects.json");
        var registry = JsonNode.Parse(File.ReadAllText(manifestPath))!;
        var project = registry["projects"]!.AsArray().Single(row => row!["path"]!.ToString() == CurrentExecutionContractTests.CandidateFixture.First)!;
        project["references"] = new JsonArray(CurrentExecutionContractTests.CandidateFixture.Second);
        project["build_inputs"] = new JsonArray(configuration);
        File.WriteAllText(manifestPath, registry.ToJsonString());
        fixture.Tree.Track();
        fixture.Run();
        fixture.Seed();
        var path = changed switch
        {
            "reference-source" => referenceSource,
            "reference-project" => CurrentExecutionContractTests.CandidateFixture.Second,
            _ => configuration,
        };
        File.AppendAllText(Path.Combine(fixture.Root, path), "\n");
        fixture.Tree.Track();

        fixture.Run();

        Assert.Equal(expected, fixture.Calls.Count);
    }

    private static void RegisterCheckPrograms(ReportInputsFixture fixture)
    {
        foreach (var path in new[] { ProgramA, ProgramB, SharedProgram }) fixture.Tree.Write(path, "class Input {}\n");
        fixture.Edit(rows =>
        {
            rows.Single(row => row!["id"]!.ToString() == "SL-015")!["program_inputs"] = new JsonArray(ProgramA, SharedProgram);
            rows.Single(row => row!["id"]!.ToString() == "SL-019")!["program_inputs"] = new JsonArray(ProgramB, SharedProgram);
        });
        fixture.Tree.Track();
    }
}
