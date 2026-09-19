using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CommonCheckExecutionTests
{
    [Fact]
    public void ReadOnlyValidationReusesItsCompleteCheckRegistration()
    {
        using var fixture = new Fixture();
        var validation = CommonExecutionEvidence.ValidationScope.Create(fixture.Tree.Root);
        var previous = CommonExecutionEvidence.ReadingCheckManifest.Value;
        var reads = 0;
        CommonExecutionEvidence.ReadingCheckManifest.Value = () => reads++;
        try
        {
            var checks = validation.CheckManifest();
            Assert.Equal(25, checks.Count);
            Assert.Equal(CommonCheckRegistrationFixture.Ids, checks.Select(check => check.Id));
            var expected = JsonSerializer.Serialize(checks);
            var repeated = validation.CheckManifest();
            Assert.NotSame(checks, repeated);
            Assert.Equal(expected, JsonSerializer.Serialize(repeated));

            checks[0].ProgramProjects[0] = "tools/Corrupt.csproj";
            checks[0].ProgramInputs[0] = "tools/Corrupt.cs";
            Assert.Equal(expected, JsonSerializer.Serialize(validation.CheckManifest()));
            Assert.Equal(expected, JsonSerializer.Serialize(validation.Fresh().CheckManifest()));
            Assert.Equal(1, reads);
        }
        finally { CommonExecutionEvidence.ReadingCheckManifest.Value = previous; }
    }

    [Fact]
    public void FreshValidationReadsChangedRegistrationWithoutSharingAnotherRepository()
    {
        using var first = new Fixture();
        using var second = new Fixture();
        var original = CommonExecutionEvidence.ValidationScope.Create(first.Tree.Root).CheckManifest();
        CommonExecutionEvidence.Write(first.Tree.Root, CommonExecutionEvidence.CheckManifestPath,
            new CommonCheckManifest("ci-check-input-registration-v3", original.Select(check => check.Id == "filemap"
                ? check with { Materials = ["fixtures/selftest.txt"] } : check).ToArray()));

        var changed = CommonExecutionEvidence.ValidationScope.Create(first.Tree.Root).CheckManifest();
        var other = CommonExecutionEvidence.ValidationScope.Create(second.Tree.Root).CheckManifest();
        Assert.Equal(new[] { "fixtures/selftest.txt" }, changed.Single(check => check.Id == "filemap").Materials);
        Assert.Empty(other.Single(check => check.Id == "filemap").Materials);
        Assert.NotSame(original, changed);
        Assert.NotSame(changed, other);
    }

    [Theory]
    [InlineData("project", "tools/Absent.csproj")]
    [InlineData("material", "fixtures/absent.txt")]
    public void FreshValidationRejectsDamagedUnselectedRegistration(string defect, string expected)
    {
        using var fixture = new Fixture();
        fixture.Run();
        var original = CommonExecutionEvidence.ValidationScope.Create(fixture.Tree.Root).CheckManifest();
        CommonExecutionEvidence.Write(fixture.Tree.Root, CommonExecutionEvidence.CheckManifestPath,
            new CommonCheckManifest("ci-check-input-registration-v3", original.Select(check => check.Id != "SL-001" ? check
                : defect == "project" ? check with { ProgramProjects = [expected] }
                : check with { Materials = [expected] }).ToArray()));

        var fresh = CommonExecutionEvidence.ValidationScope.Create(fixture.Tree.Root);
        var error = Assert.Throws<InvalidDataException>(() => fresh.CheckManifest());
        Assert.Contains("SL-001", error.Message, StringComparison.Ordinal);
        Assert.Contains(expected, error.Message, StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => fresh.CheckManifest());
        Assert.Throws<InvalidDataException>(() => fixture.Run());
        Assert.Empty(fixture.Calls);
    }

    [Theory]
    [InlineData("changed")]
    [InlineData("missing")]
    public void FreshSeedValidationRejectsPreviouslyAcceptedMaterialDamage(string damage)
    {
        using var fixture = new Fixture();
        fixture.Run();
        fixture.Seed();
        var accepted = CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Tree.Root, "engineering");
        var material = accepted.Units.SelectMany(unit => unit.Materials).First();
        var path = Path.Combine(fixture.Tree.Root, CommonExecutionEvidence.CheckSeedPath("engineering"), material.Path);
        if (damage == "changed")
        {
            File.AppendAllText(path, "changed after acceptance");
            var error = Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Tree.Root, "engineering"));
            Assert.Contains(material.Path, error.Message, StringComparison.Ordinal);
        }
        else
        {
            File.Delete(path);
            Assert.Throws<FileNotFoundException>(() => CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Tree.Root, "engineering"));
        }
    }

    [Theory]
    [InlineData("existing")]
    [InlineData("missing")]
    [InlineData("corrupt")]
    public void EngineeringSeedTransportPreservesSourceAndProvenanceAcrossTestSeedStates(string state)
    {
        using var fixture = new Fixture();
        var originalChecks = fixture.Run();
        fixture.Seed();
        var root = fixture.Tree.Root;
        SharedBuildContractTests.Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qam", "registered seed material");
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var build = CommonExecutionEvidence.ValidateBuild(root);
        var engineering = CommonExecutionEvidence.ValidateEngineering(root);
        var tests = CommonExecutionEvidence.ValidateTests(root);
        var source = build.Materials.Concat(engineering.Materials).Select(material => material.Path)
            .Append(CommonExecutionEvidence.EngineeringPath).Distinct(StringComparer.Ordinal)
            .ToDictionary(path => path, path => File.ReadAllBytes(Path.Combine(root, path)), StringComparer.Ordinal);
        var testSeed = Path.Combine(root, CommonExecutionEvidence.TestSeedPath);
        if (state == "missing") Directory.Delete(testSeed, recursive: true);
        if (state == "corrupt") File.AppendAllText(Path.Combine(testSeed, tests.Materials[0].Path), "corrupt optional TRX");

        var archive = Path.Combine(root, "build/seed-material.tgz");
        using var output = new StringWriter();
        string[] Options(string action) => [action, "--repository", root, "--stage", "engineering-seed",
            "--commit", commit, "--run-id", "17", "--run-attempt", "2"];
        Assert.Equal(0, Program.Run([.. Options("transport-pack"), "--archive", archive], TestResultEvidence.Load, output, output));
        Assert.True(File.Exists(archive));
        Assert.Equal(0, Program.Run(Options("transport-verify"), TestResultEvidence.Load, output, output));

        Assert.Equal(build.Candidate, CommonExecutionEvidence.Candidate(root));
        foreach (var (path, bytes) in source) Assert.Equal(bytes, File.ReadAllBytes(Path.Combine(root, path)));
        var exportedChecks = CommonExecutionEvidence.ValidateCheckSeedBundle(root, "engineering");
        Assert.Equal(originalChecks.Candidate, exportedChecks.Candidate);
        Assert.Equal(originalChecks.Round, exportedChecks.Round);
        Assert.Equal(File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.ChecksPath("engineering"))),
            File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.CheckSeedPath("engineering"), "checks.json")));
        var exportedTests = CommonExecutionEvidence.Read<TestExecutionRecord>(testSeed, "tests.json");
        Assert.Equal(tests.Candidate, exportedTests.Candidate);
        Assert.Equal(tests.Round, exportedTests.Round);
        Assert.Equal(tests.Projects, exportedTests.Projects);
        Assert.Equal(tests.Materials, exportedTests.Materials);
        foreach (var material in tests.Materials)
            Assert.Equal(source[material.Path], File.ReadAllBytes(Path.Combine(testSeed, material.Path)));
    }

    [Fact]
    public void FallbackSeedNotificationFollowsCompleteCopyAndNextExportRechecksSource()
    {
        using var fixture = new Fixture();
        var original = fixture.Run();
        fixture.Seed();
        var root = fixture.Tree.Root;
        Directory.Delete(Path.Combine(root, CommonExecutionEvidence.TestSeedPath), recursive: true);
        Directory.Delete(Path.Combine(root, CommonExecutionEvidence.CheckSeedPath("engineering")), recursive: true);
        CommonCheckRecord? published = null;
        Exception? notificationFailure = null;
        using var output = new SeedExportObserver(() =>
        {
            notificationFailure = Record.Exception(() => { published = CommonExecutionEvidence.ValidateCheckSeedBundle(root, "engineering"); });
            fixture.Tree.Write("fixtures/selftest.txt", "source changed after export notification");
        });

        Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "engineering", output));
        Assert.True(output.Observed);
        Assert.Null(notificationFailure);
        Assert.NotNull(published);
        Assert.Equal(original.Candidate, published.Candidate);
        Assert.Equal(original.Round, published.Round);
        Assert.NotEqual(original.Candidate, CommonExecutionEvidence.Candidate(root));
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ExportCheckSeed(root, "engineering", TextWriter.Null));
    }

    [Theory]
    [InlineData("COMMON_CHECK_SEED_SAVED")]
    [InlineData("ENGINEERING_TEST_SEED_SAVED")]
    public void SeedNotificationIOExceptionDoesNotInvalidateEngineering(string notification)
    {
        using var fixture = new Fixture();
        fixture.Run();
        fixture.Seed();
        var root = fixture.Tree.Root;
        var accepted = CommonExecutionEvidence.ValidateEngineering(root);
        if (notification == "ENGINEERING_TEST_SEED_SAVED")
            Directory.Delete(Path.Combine(root, CommonExecutionEvidence.TestSeedPath), recursive: true);
        using var output = new FailingSeedNotificationWriter(notification);
        using var error = new StringWriter();

        var exit = Program.Run(["check-seed-export", "--repository", root, "--stage", "engineering"],
            TestResultEvidence.Load, output, error);

        Assert.True(output.Failed);
        Assert.True(exit == 0, error.ToString());
        Assert.Contains("_SEED_NOT_SAVED", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
        var current = CommonExecutionEvidence.ValidateEngineering(root);
        Assert.Equal(accepted.Candidate, current.Candidate);
        Assert.Equal(accepted.Round, current.Round);
    }

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
        Assert.Equal(original.Units.Select(unit => unit.Id), fixture.Calls.Order(StringComparer.Ordinal));
        Assert.All(original.Units, unit => Assert.Equal("executed", unit.Status));
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
    [InlineData("scribe-consumer")]
    [InlineData("scribe-registration")]
    public void EitherConsumerInputOrScribeRegistrationInvalidatesConsumers(string change)
    {
        using var fixture = new ReportInputsFixture();
        fixture.Run();
        fixture.Seed();
        if (change == "lean-material") fixture.Tree.Write("fixtures/lean.txt", "changed");
        if (change == "scribe-material") fixture.Tree.Write("fixtures/scribe.txt", "changed");
        if (change == "scribe-consumer") fixture.Tree.Write(ReportInputsFixture.ScribeConsumer, ReportInputsFixture.Consumer(ReportInputsFixture.ScribeProducer, "fixtures/extra.txt"));
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

    private sealed class FailingSeedNotificationWriter(string notification) : StringWriter
    {
        internal bool Failed { get; private set; }
        public override void Write(string? value) { FailOnce(value); base.Write(value); }
        public override void WriteLine(string? value) { FailOnce(value); base.WriteLine(value); }
        private void FailOnce(string? value)
        {
            if (Failed || value is null || !value.Contains(notification, StringComparison.Ordinal)) return;
            Failed = true;
            throw new IOException("temporary seed notification write failure");
        }
    }

    private sealed class SeedExportObserver(Action observed) : StringWriter
    {
        internal bool Observed { get; private set; }
        public override void Write(char value) { base.Write(value); Observe(); }
        public override void Write(string? value) { base.Write(value); Observe(); }
        public override void WriteLine(string? value) { base.WriteLine(value); Observe(); }
        private void Observe()
        {
            if (Observed || !ToString().Contains("ENGINEERING_TEST_SEED_SAVED" + NewLine, StringComparison.Ordinal)) return;
            Observed = true;
            observed();
        }
    }

    private sealed class ReportInputsFixture : IDisposable
    {
        internal const string LeanProducer = "Meta/ReportProducers/lean.json";
        internal const string ScribeProducer = "Meta/ReportProducers/scribe.json";
        internal const string LeanConsumer = "Meta/ReportConsumers/lean.json";
        internal const string ScribeConsumer = "Meta/ReportConsumers/scribe.json";
        private readonly Fixture fixture = new();
        internal CurrentExecutionContractTests.CandidateFixture Tree => fixture.Tree;
        internal string Root => Tree.Root;
        internal List<string> Calls { get; } = [];
        internal string ScribeMaterial { get; set; } = CommonCheckRegistrationFixture.ScribeMaterial;
        internal const string NativeRegistration = "lean-report-inputs.json";
        internal static string Producer(string scope) => System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "report-producer-scope-v2", registration = NativeRegistration, scope, projects = Array.Empty<string>(),
        });
        internal static string Consumer(string producer, string material) => System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "report-consumer-inputs-v2", producer, projects = Array.Empty<string>(), program_inputs = new[] { material }, materials = new[] { material },
        });
        internal ReportInputsFixture()
        {
            Tree.Write(NativeRegistration, """
                {"producer_scopes":{"lean-report":{"include":[],"exclude":[]},"scribe-content":{"include":[],"exclude":[]}}}
                """);
            Tree.Write(LeanProducer, Producer("lean-report"));
            Tree.Write(ScribeProducer, Producer("scribe-content"));
            Tree.Write(LeanConsumer, Consumer(LeanProducer, "fixtures/lean.txt"));
            Tree.Write(ScribeConsumer, Consumer(ScribeProducer, "fixtures/scribe.txt"));
            foreach (var path in new[] { "fixtures/lean.txt", "fixtures/scribe.txt", "fixtures/extra.txt" }) Tree.Write(path, "input");
            Edit(rows =>
            {
                JsonNode Input(string producer, string artifact) => JsonNode.Parse("{\"producer\":\"" + producer + "\",\"consumer\":\"" + (producer == LeanProducer ? LeanConsumer : ScribeConsumer) + "\",\"artifact\":\"" + artifact + "\",\"materials\":[\"global.json\"]}")!;
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
