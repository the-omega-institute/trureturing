using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CommonCheckExecutionTests
{
    [Fact]
    public void ActualRepositoryRegistrationReachesEngineeringSeedHandling()
    {
        using var output = new StringWriter();
        var exit = Program.Run(["check-seed-import", "--repository", TestRepositoryLayout.FindRoot(), "--stage", "engineering"],
            TestResultEvidence.Load, output, output);
        Assert.True(exit == 0, output.ToString());
        Assert.Contains("COMMON_CHECK_SEED_IMPORTED stage=engineering", output.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void DistinctReportAndScribeInputsShareProducerAndRetainOriginalEvidence()
    {
        using var fixture = new ReportInputsFixture();
        var original = fixture.Run();
        Assert.Equal(1, fixture.Calls.Count(id => id == "scribe-describe"));
        Assert.Equal(22, fixture.Calls.Count);
        foreach (var id in new[] { "SL-006", "SL-023" })
        {
            var predicate = original.Units.Single(unit => unit.Id == id);
            Assert.NotNull(predicate.Report);
            Assert.NotNull(predicate.Data);
            Assert.Equal(CommonCheckRegistrationFixture.ScribeMaterial, File.ReadAllText(Path.Combine(fixture.Root, predicate.Data)));
        }
        fixture.Seed();
        fixture.Tree.Write("unrelated.txt", "new candidate");
        fixture.Tree.Track();
        var warm = fixture.Run();
        Assert.Empty(fixture.Calls);
        Assert.NotEqual(original.Candidate, warm.Candidate);
        foreach (var unit in warm.Units)
        {
            var previous = original.Units.Single(row => row.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(previous.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(previous.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(previous.Data, unit.Data);
            Assert.Equal(previous.Materials, unit.Materials);
        }
    }

    [Theory]
    [InlineData("lean-material")]
    [InlineData("scribe-material")]
    [InlineData("scribe-producer")]
    [InlineData("scribe-registration")]
    public void EitherProducerInputOrScribeRegistrationInvalidatesConsumers(string change)
    {
        using var fixture = new ReportInputsFixture();
        fixture.Run();
        fixture.Seed();
        if (change == "lean-material") fixture.Tree.Write("fixtures/lean.txt", "changed");
        if (change == "scribe-material") fixture.Tree.Write("fixtures/scribe.txt", "changed");
        if (change == "scribe-producer") fixture.Tree.Write(ReportInputsFixture.ScribeProducer, ReportInputsFixture.Producer("fixtures/extra.txt"));
        if (change == "scribe-registration") fixture.Edit(rows => rows.Single(row => row!["id"]!.ToString() == "scribe-describe")!["materials"] = new JsonArray("fixtures/extra.txt"));
        fixture.Tree.Track();
        fixture.Run();
        Assert.Equal(change == "lean-material" ? new[] { "SL-006" } : new[] { "SL-006", "SL-023", "scribe-describe" }, fixture.Calls.Order(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData("duplicate", "raw-lean-report")]
    [InlineData("conflicting", "raw-lean-report")]
    [InlineData("artifact", "unknown-artifact")]
    [InlineData("producer", "Meta/ReportProducers/absent.json")]
    [InlineData("scribe-producer", "Meta/ReportProducers/lean.json")]
    public void DuplicateConflictingOrUnknownReportDeclarationNamesObject(string defect, string expected)
    {
        using var fixture = new ReportInputsFixture();
        fixture.Edit(rows =>
        {
            var inputs = rows.Single(row => row!["id"]!.ToString() == "SL-006")!["report_inputs"]!.AsArray();
            if (defect is "duplicate" or "conflicting")
            {
                var duplicate = inputs[0]!.DeepClone();
                if (defect == "conflicting") duplicate["producer"] = ReportInputsFixture.ScribeProducer;
                inputs.Add(duplicate);
            }
            if (defect == "artifact") inputs[1]!["artifact"] = expected;
            if (defect is "producer" or "scribe-producer") inputs[1]!["producer"] = expected;
        });
        var error = Assert.Throws<InvalidDataException>(() => fixture.Run());
        Assert.Contains("SL-006", error.Message, StringComparison.Ordinal);
        Assert.Contains(expected, error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Fact]
    public void DeclaredInputsStillRequireCurrentReport()
    {
        using var fixture = new ReportInputsFixture();
        File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath));
        var error = Assert.ThrowsAny<Exception>(() => fixture.Run());
        Assert.Contains("raw-lean-report", error.Message, StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Fact]
    public void ScribeDependentPredicateRequiresCompletedProducer()
    {
        using var fixture = new ReportInputsFixture();
        var error = Assert.Throws<InvalidDataException>(() =>
        {
            var checks = CommonExecutionEvidence.BeginChecks(fixture.Root, "current", fixture.Tree.Build(), TextWriter.Null);
            checks.Run("SL-006", () => new([new("SL-006", 0, CommonCheckRegistrationFixture.Predicate("SL-006"))]));
        });
        Assert.Contains("Scribe", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("invalid")]
    public void ScribeSeedMaterialDamageInvalidatesDependentPredicates(string damage)
    {
        using var fixture = new ReportInputsFixture();
        fixture.Run();
        fixture.Seed();
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var path = Path.Combine(seed, "checks.json");
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        var unit = doc["units"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-006")!;
        Assert.NotNull(unit["data"]);
        var data = unit["data"]!.ToString();
        if (damage == "missing") File.Delete(Path.Combine(seed, data));
        else
        {
            File.WriteAllText(Path.Combine(seed, data), "{\"Version\":2,\"Records\":[],\"References\":[],\"Latex\":[]}");
            unit["materials"]!.AsArray().Single(row => row!["path"]!.ToString() == data)!["sha256"] = CommonExecutionEvidence.Hash(Path.Combine(seed, data));
            File.WriteAllText(path, doc.ToJsonString());
        }
        fixture.Run();
        Assert.Equal(new[] { "SL-006" }, fixture.Calls);
    }

    [Fact]
    public void ChangedVerifiedScribeValueInvalidatesPredicatesBeforeSelection()
    {
        using var fixture = new ReportInputsFixture();
        fixture.Run();
        fixture.Seed();
        var path = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"), "checks.json");
        var doc = JsonNode.Parse(File.ReadAllText(path))!;
        var units = doc["units"]!.AsArray();
        units.Remove(units.Single(row => row!["id"]!.ToString() == "scribe-describe"));
        File.WriteAllText(path, doc.ToJsonString());
        fixture.ScribeMaterial = "{\"Version\":1,\"Records\":[],\"References\":[\"D5/S0/Carrier/Ring.goldenRing\"],\"Latex\":[]}";
        fixture.Run(checks => Assert.Equal(new[] { "SL-006", "SL-023" }, checks.Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal) && checks.IsSelected(id))));
        Assert.Equal(new[] { "scribe-describe", "SL-006", "SL-023" }, fixture.Calls);
    }

    private sealed class ReportInputsFixture : IDisposable
    {
        internal const string LeanProducer = "Meta/ReportProducers/lean.json";
        internal const string ScribeProducer = "Meta/ReportProducers/scribe.json";
        private readonly Fixture fixture = new();
        internal CurrentExecutionContractTests.CandidateFixture Tree => fixture.Tree;
        internal string Root => Tree.Root;
        internal List<string> Calls { get; } = [];
        internal string ScribeMaterial { get; set; } = CommonCheckRegistrationFixture.ScribeMaterial;
        internal static string Producer(string material) => "{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"materials\":[\"" + material + "\"]}";
        internal ReportInputsFixture()
        {
            Tree.Write(LeanProducer, Producer("fixtures/lean.txt"));
            Tree.Write(ScribeProducer, Producer("fixtures/scribe.txt"));
            foreach (var path in new[] { "fixtures/lean.txt", "fixtures/scribe.txt", "fixtures/extra.txt" }) Tree.Write(path, "input");
            Edit(rows =>
            {
                JsonNode Input(string producer, string artifact) => JsonNode.Parse("{\"producer\":\"" + producer + "\",\"artifact\":\"" + artifact + "\",\"materials\":[\"global.json\"]}")!;
                JsonNode Row(string id) => rows.Single(row => row!["id"]!.ToString() == id)!;
                Row("SL-006")["report_inputs"] = new JsonArray(Input(LeanProducer, "raw-lean-report"), Input(ScribeProducer, "VerifiedScribeEmissions"));
                Row("SL-023")["report_inputs"] = new JsonArray(Input(ScribeProducer, "VerifiedScribeEmissions"));
                Row("scribe-describe")["report_inputs"] = new JsonArray(Input(ScribeProducer, "raw-lean-report"));
            });
            Tree.Track();
            CiTransportTests.Report(Root);
        }
        internal void Edit(Action<JsonArray> edit)
        {
            var path = Path.Combine(Root, CommonExecutionEvidence.CheckManifestPath);
            var doc = JsonNode.Parse(File.ReadAllText(path))!;
            edit(doc["checks"]!.AsArray());
            File.WriteAllText(path, doc.ToJsonString());
        }
        internal CommonCheckRecord Run(Action<CommonExecutionEvidence.CheckExecution>? afterScribe = null)
        {
            Calls.Clear();
            var build = Tree.Build();
            var checks = CommonExecutionEvidence.BeginChecks(Root, "current", build, TextWriter.Null);
            checks.Run("scribe-describe", () => { Calls.Add("scribe-describe"); return new([new("scribe-describe", 0, "verified")], ScribeMaterial); });
            afterScribe?.Invoke(checks);
            foreach (var id in checks.Ids.Where(id => id != "scribe-describe")) checks.Run(id, () =>
            {
                Calls.Add(id);
                return new([new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal) ? CommonCheckRegistrationFixture.Predicate(id) : "passed")]);
            });
            var record = checks.Seal();
            CommonExecutionEvidence.SealCurrent(Root, build, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-build.log")).ToArray());
            return record;
        }
        internal void Seed() => Assert.True(CommonExecutionEvidence.ExportCheckSeed(Root, "current", TextWriter.Null));
        public void Dispose() => fixture.Dispose();
    }
}
