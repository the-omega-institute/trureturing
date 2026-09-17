using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CommonCheckExecutionTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TransportInputChangeReusesChecksAgainstTheValidatedReport(bool changeDeclaration)
    {
        using var fixture = new ReportInputsFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, ReportInputsFixture.NativeRegistration)))!;
        foreach (var scope in registration["producer_scopes"]!.AsObject())
            scope.Value!["include"] = JsonNode.Parse("[{\"pattern\":\"fixtures/transport.py\",\"optional\":false}]");
        fixture.Tree.Write(ReportInputsFixture.NativeRegistration, registration.ToJsonString());
        fixture.Tree.Write("fixtures/transport.py", "transport version one");
        fixture.Tree.Track();
        var original = fixture.Run();
        fixture.Seed();
        fixture.Tree.Write("fixtures/transport.py", "transport version two");
        if (changeDeclaration)
        {
            fixture.Tree.Write("fixtures/extra-transport.py", "additional transport input");
            foreach (var scope in registration["producer_scopes"]!.AsObject())
                scope.Value!["include"]!.AsArray().Add(JsonNode.Parse("{\"pattern\":\"fixtures/extra-transport.py\",\"optional\":false}"));
            fixture.Tree.Write(ReportInputsFixture.NativeRegistration, registration.ToJsonString());
        }
        fixture.Tree.Track();
        var current = fixture.Run();
        Assert.Empty(fixture.Calls);
        Assert.All(current.Units, unit => Assert.Equal("reused", unit.Status));
        Assert.Equal(original.Units.Select(unit => unit.ExecutionRound), current.Units.Select(unit => unit.ExecutionRound));
        Assert.Equal(original.Units.Select(unit => unit.Materials), current.Units.Select(unit => unit.Materials));
    }

    [Theory]
    [InlineData("missing-reference", "consumer")]
    [InlineData("missing-manifest", "Meta/ReportConsumers/lean.json")]
    [InlineData("wrong-producer", "Meta/ReportConsumers/lean.json")]
    [InlineData("missing-material", "fixtures/absent.txt")]
    [InlineData("duplicate-material", "fixtures/lean.txt")]
    [InlineData("missing-projects", "Meta/ReportConsumers/lean.json")]
    [InlineData("unknown-project", "tools/Absent/Absent.csproj")]
    [InlineData("unknown-schema", "Meta/ReportConsumers/lean.json")]
    [InlineData("unknown-field", "Meta/ReportConsumers/lean.json")]
    public void ConsumerRegistrationDefectsFailBeforeRunningChecks(string defect, string expected)
    {
        using var fixture = new ReportInputsFixture();
        var path = ReportInputsFixture.LeanConsumer;
        var consumer = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, path)))!.AsObject();
        if (defect == "missing-reference") fixture.Edit(rows =>
            rows.Single(row => row!["id"]!.ToString() == "SL-006")!["report_inputs"]![0]!.AsObject().Remove("consumer"));
        if (defect == "wrong-producer") consumer["producer"] = ReportInputsFixture.ScribeProducer;
        if (defect == "missing-material") consumer["materials"] = new JsonArray("fixtures/absent.txt");
        if (defect == "duplicate-material") consumer["materials"] = new JsonArray("fixtures/lean.txt", "fixtures/lean.txt");
        if (defect == "missing-projects") consumer.Remove("projects");
        if (defect == "unknown-project") consumer["projects"] = new JsonArray("tools/Absent/Absent.csproj");
        if (defect == "unknown-schema") consumer["schema"] = "unknown-schema";
        if (defect == "unknown-field") consumer["unexpected"] = true;
        fixture.Tree.Write(path, consumer.ToJsonString());
        if (defect == "missing-manifest") File.Delete(Path.Combine(fixture.Root, path));
        fixture.Tree.Track();
        var error = Assert.Throws<InvalidDataException>(() => fixture.Run());
        Assert.Contains(expected, error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Fact]
    public void ExplicitConsumerCompatibilityMaterialInvalidatesConsumers()
    {
        using var fixture = new ReportInputsFixture();
        fixture.Tree.Write("fixtures/compatibility.txt", "version one");
        fixture.Tree.Write(ReportInputsFixture.LeanConsumer,
            ReportInputsFixture.Consumer(ReportInputsFixture.LeanProducer, "fixtures/compatibility.txt"));
        fixture.Tree.Track();
        fixture.Run();
        fixture.Seed();
        fixture.Tree.Write("fixtures/compatibility.txt", "version two");
        fixture.Tree.Track();
        fixture.Run();
        Assert.Equal(new[] { "SL-006" }, fixture.Calls);
    }

    [Fact]
    public void DeclaredConsumerProgramChangeInvalidatesConsumers()
    {
        using var fixture = new ReportInputsFixture();
        var consumer = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, ReportInputsFixture.LeanConsumer)))!;
        consumer["projects"] = new JsonArray(CurrentExecutionContractTests.CandidateFixture.Second);
        fixture.Tree.Write(ReportInputsFixture.LeanConsumer, consumer.ToJsonString());
        fixture.Tree.Write("tools/tests/Second/Consumer.cs", "class Consumer { }");
        fixture.Tree.Track();
        fixture.Run();
        fixture.Seed();
        fixture.Tree.Write("tools/tests/Second/Consumer.cs", "class Consumer { public int Version => 2; }");
        fixture.Tree.Track();
        fixture.Run();
        Assert.Equal(new[] { "SL-006" }, fixture.Calls);
    }
}
