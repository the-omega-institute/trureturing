using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class CurrentSeedCoverageTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Fact]
    public void TransportedProducerCanSelectAndPublishWithoutLeanTools()
    {
        using var fixture = Prepare();
        Producer(fixture, "prepare");
        fixture.CommitPlan();
        fixture.Processes();
        FullCurrent(fixture, []);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        Producer(fixture, "probe-without-tools");
    }

    [Fact]
    public void CurrentProducerSeedSurvivesReusedChecksAndFollowingMetadataOnlyCurrent()
    {
        using var fixture = Prepare();
        const string producer = "producer.py";
        Producer(fixture, "prepare");
        fixture.CommitPlan();
        fixture.Processes();
        var oldReceipt = File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".reuse.json"));
        var original = FullCurrent(fixture, []);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var originalReport = File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath));

        fixture.Write(producer, "# producer version two\n");
        fixture.CommitPlan();
        fixture.Processes();
        Producer(fixture, "renew");
        var newReceipt = File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".reuse.json"));
        Assert.NotEqual(oldReceipt, newReceipt);
        var calls = new List<string>();
        var current = FullCurrent(fixture, calls);
        Assert.Empty(calls);
        Assert.Equal(originalReport, File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)));
        Assert.All(current.Units, unit =>
        {
            var previous = original.Units.Single(row => row.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(previous.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(previous.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(previous.Materials, unit.Materials);
        });
        var accepted = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var descriptorPath = Path.Combine(seed, "producer-report.json");
        Assert.True(File.Exists(descriptorPath), "accepted canonical producer must survive reused report checks");
        var descriptor = File.ReadAllText(descriptorPath);
        var producerRecord = JsonNode.Parse(descriptor)!;
        Assert.Equal(accepted.Candidate, producerRecord["candidate"]!.ToString());
        Assert.Equal(accepted.Round, producerRecord["round"]!.ToString());
        Assert.Equal(CommonExecutionEvidence.ReportPath, producerRecord["report"]!.ToString());
        Assert.Equal(newReceipt, File.ReadAllText(Path.Combine(seed, CommonExecutionEvidence.ReportPath + ".reuse.json")));
        var previousReport = original.Units.First(unit => unit.Report is not null).Report!;
        Assert.Equal(oldReceipt, File.ReadAllText(Path.Combine(seed, previousReport + ".reuse.json")));
        CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        Producer(fixture, "probe");

        fixture.Write(Input, "metadata-only next candidate\n");
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        RunSelectedWithoutOriginalMaterials(fixture);
        // The selected route has no report producer. Even an unrelated stale
        // canonical file must not replace the last accepted producer identity.
        fixture.Write(CommonExecutionEvidence.ReportPath + ".reuse.json", "unaccepted stale receipt\n");
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        Assert.Equal(descriptor, File.ReadAllText(descriptorPath));
        Assert.Equal(newReceipt, File.ReadAllText(Path.Combine(seed, CommonExecutionEvidence.ReportPath + ".reuse.json")));
        CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        Producer(fixture, "probe");
    }

    [Fact]
    public void ProducedReportExportsWhenEverySelectedCheckIsReportIndependent()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean-report", "filemap"]);
        Producer(fixture, "prepare");
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var stageOutput = new StringWriter();
        Assert.True(fixture.Run("current", stageOutput) == 0, stageOutput.ToString());
        var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"));
        Assert.Null(Assert.Single(checks.Units).Report);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        Producer(fixture, "probe");
    }

    [Theory]
    [InlineData("receipt")]
    [InlineData("descriptor")]
    public void DamagedProducerSeedCannotAuthorizeReportReuse(string defect)
    {
        using var fixture = Prepare();
        Producer(fixture, "prepare");
        fixture.CommitPlan();
        fixture.Processes();
        FullCurrent(fixture, []);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var path = Path.Combine(seed, defect == "receipt" ? CommonExecutionEvidence.ReportPath + ".reuse.json" : "producer-report.json");
        Assert.True(File.Exists(path), "producer evidence must be exported before damage");
        if (defect == "receipt") File.WriteAllText(path, "damaged optional producer evidence\n");
        else
        {
            var descriptor = JsonNode.Parse(File.ReadAllText(path))!;
            descriptor["round"] = new string('z', 32);
            File.WriteAllText(path, descriptor.ToJsonString());
        }
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current"));
        Producer(fixture, "probe-miss");
    }

    [Fact]
    public void ProducerMutationAfterAcceptanceCannotReplacePreviousSeed()
    {
        using var fixture = Prepare();
        fixture.Write(CommonExecutionEvidence.ReportPath + ".reuse.json", "accepted receipt\n");
        var checks = FullCurrent(fixture, []);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var accepted = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var previous = File.ReadAllText(Path.Combine(seed, "producer-report.json"));
        fixture.Write(CommonExecutionEvidence.ReportPath + ".reuse.json", "changed after acceptance\n");
        Assert.False(CommonExecutionEvidence.CopyAcceptedCheckSeed(fixture.Root, "current", accepted,
            null, checks, TextWriter.Null));
        Assert.Equal(previous, File.ReadAllText(Path.Combine(seed, "producer-report.json")));
        Assert.Equal("accepted receipt\n", File.ReadAllText(Path.Combine(seed, CommonExecutionEvidence.ReportPath + ".reuse.json")));
        CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void OptionalProducerReceiptTravelsWithItsReportAndRetainsItsHash(bool receipt, bool damage)
    {
        using var fixture = Prepare();
        const string suffix = ".reuse.json";
        if (receipt) fixture.Write(CommonExecutionEvidence.ReportPath + suffix, "opaque producer-owned receipt\n");
        var original = FullCurrent(fixture, []);
        var unit = original.Units.Single(row => row.Id == "SL-001");
        var path = unit.Report + suffix;
        Assert.Equal(receipt, unit.Materials.Any(material => material.Path == path));
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Equal(receipt, current.Materials.Any(material => material.Path == CommonExecutionEvidence.ReportPath + suffix));
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        Assert.Equal(receipt, File.Exists(Path.Combine(seed, path)));
        if (damage)
        {
            File.WriteAllText(Path.Combine(seed, path), "replaced receipt\n");
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current"));
        }
        else
        {
            var accepted = CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
            Assert.Equal(unit.Materials, accepted.Units.Single(row => row.Id == "SL-001").Materials);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedCurrentSnapshotPreservesPreviouslyAcceptedUnselectedUnits(bool selectedInputChanges)
    {
        using var fixture = Prepare();
        var calls = new List<string>();
        var original = FullCurrent(fixture, calls);
        Assert.Equal(22, calls.Count);
        Assert.NotNull(original.Units.Single(unit => unit.Id == "SL-001").Report);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        Assert.Equal(22, CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current").Units.Length);

        if (selectedInputChanges)
        {
            fixture.Write(Input, "changed selected input\n");
            fixture.CommitPlan();
            fixture.Processes(prepareReport: false);
        }
        var selected = RunSelectedWithoutOriginalMaterials(fixture);
        Assert.Equal(selectedInputChanges ? "executed" : "reused", selected.Status);
        var selectedSeed = CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        var final = FullCurrent(fixture, calls);
        output.WriteLine("CURRENT_SEED_COVERAGE full={0} selected={1} selected_status={2} exported={3} final_executed={4} final_reused={5}",
            original.Units.Length, selected.Id, selected.Status, selectedSeed.Units.Length, calls.Count,
            final.Units.Count(unit => unit.Status == "reused"));
        Assert.Empty(calls);
        Assert.Equal(22, final.Units.Length);
        foreach (var unit in final.Units)
        {
            var expected = unit.Id == "filemap" ? selected : original.Units.Single(row => row.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(expected.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(expected.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(expected.ExecutionEnvironment, unit.ExecutionEnvironment);
            Assert.Equal(expected.InputFingerprint, unit.InputFingerprint);
            Assert.Equal(expected.Result, unit.Result);
            Assert.Equal(expected.Operations, unit.Operations);
            Assert.Equal(expected.Data, unit.Data);
            Assert.Equal(expected.Report, unit.Report);
            Assert.Equal(expected.Materials, unit.Materials);
        }
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("null-unit")]
    [InlineData("null-material")]
    public void DamagedOldAcceptanceCannotBeNormalizedIntoReusableEvidence(string defect)
    {
        using var fixture = Prepare();
        var calls = new List<string>();
        FullCurrent(fixture, calls);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var seedPath = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"), "checks.json");
        var seed = JsonNode.Parse(File.ReadAllText(seedPath))!;
        if (defect is "candidate" or "round") seed[defect] = new string('0', defect == "candidate" ? 64 : 32);
        else if (defect == "null-unit") seed["units"]![0] = null;
        else seed["units"]![0]!["materials"]![0] = null;
        File.WriteAllText(seedPath, seed.ToJsonString());

        RunSelectedWithoutOriginalMaterials(fixture);
        var exported = CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        var final = FullCurrent(fixture, calls);
        Assert.Equal(21, calls.Count);
        Assert.Equal("filemap", Assert.Single(exported.Units).Id);
        Assert.Equal("filemap", Assert.Single(final.Units, unit => unit.Status == "reused").Id);
    }

    [Fact]
    public void SelectedSnapshotRetainsOnlyCurrentlyRegisteredOldUnits()
    {
        using var fixture = Prepare();
        var calls = new List<string>();
        FullCurrent(fixture, calls);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        var seedRoot = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var seed = CommonExecutionEvidence.Read<CommonCheckRecord>(seedRoot, "checks.json");
        CommonExecutionEvidence.Write(seedRoot, "checks.json", seed with
        {
            Units = [.. seed.Units, seed.Units[0] with { Id = "unregistered-old-unit" }],
        });

        RunSelectedWithoutOriginalMaterials(fixture);
        var exported = CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current");
        Assert.DoesNotContain(exported.Units, unit => unit.Id == "unregistered-old-unit");
        FullCurrent(fixture, calls);
        Assert.Empty(calls);
        Assert.Equal(22, exported.Units.Length);
    }

    private const string Input = "fixtures/filemap-input.txt";

    private static void Producer(ResourceRouteTests.ResourceFixture fixture, string operation)
    {
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c", """
            import pathlib, shutil, sys
            repository, root = map(pathlib.Path, sys.argv[1:3])
            operation, relative = sys.argv[3:]
            sys.path.insert(0, str(repository / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication, reuse
            fixture = ReuseTests()
            fixture.setUp()
            try:
                if operation == 'prepare':
                    fixture.register_toolchain()
                    paths = ('D5/A.lean', 'Audit.lean', 'Inspector.lean', 'producer.py',
                        'lean-toolchain', 'lakefile.toml', 'lean-report-inputs.json', 'bin/lake', 'bin/lean',
                        'tools/scripts/report/lean-report-selection.py', 'tools/scripts/report/lean-report-input.sh',
                        'tools/scripts/worktree/lean-cache-input.sh')
                    for relative_source in paths:
                        target = root / relative_source
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(fixture.root / relative_source, target)
                    for name in ('reuse.py', 'publication.py', 'materials.py'):
                        target = root / 'tools/lean-inspector' / name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(repository / 'tools/lean-inspector' / name, target)
                fixture.root = root
                fixture.report = root / relative
                fixture.report.parent.mkdir(parents=True, exist_ok=True)
                fixture.lake = root / 'bin/lake'
                if operation in ('prepare', 'renew'):
                    if operation == 'renew':
                        assert reuse.probe(root, fixture.report, fixture.lake)['needs_lake'], 'old producer must miss'
                    fixture.receipt()
                elif operation in ('probe', 'probe-miss', 'probe-without-tools'):
                    sys.path.insert(0, str(repository / 'tools/scripts/worktree'))
                    import lean_actions
                    lake = fixture.lake
                    if operation == 'probe-without-tools':
                        fixture.lake.unlink()
                        fixture.lake.with_name('lean').unlink()
                        lake = None
                    selected = lean_actions.report_seed(root, lake)
                    if operation == 'probe-miss':
                        assert selected is None, 'damaged producer must return to normal production'
                        sys.exit(0)
                    expected = root / 'build/ci/current-check-seed' / relative
                    assert selected == str(expected), 'must select accepted independent producer: ' + str(selected)
                    assert not reuse.probe(root, pathlib.Path(selected), lake)['needs_lake']
                    output = root / 'build/reused-report' / publication.RAW
                    assert not reuse.reuse(root, pathlib.Path(selected), output, lake)['needs_lake']
                    assert output.read_bytes() == expected.read_bytes()
                else:
                    raise AssertionError(operation)
            finally:
                fixture.doCleanups()
            """, TestRepositoryLayout.FindRoot(), fixture.Root, operation, CommonExecutionEvidence.ReportPath],
            hangGuard: TestBudgets.ScriptProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
    }

    private static ResourceRouteTests.ResourceFixture Prepare()
    {
        var fixture = new ResourceRouteTests.ResourceFixture(["filemap"], Input);
        fixture.Write("Meta/ReportProducers/check.json", "{\"schema\":\"report-producer-scope-v2\",\"registration\":\"lean-report-inputs.json\",\"scope\":\"lean-report\",\"projects\":[]}");
        fixture.Write("lean-report-inputs.json", "{\"producer_scopes\":{\"lean-report\":{\"include\":[{\"pattern\":\"global.json\",\"optional\":false}],\"exclude\":[]}}}");
        fixture.Write("Meta/ReportConsumers/check.json", "{\"schema\":\"report-consumer-inputs-v1\",\"producer\":\"Meta/ReportProducers/check.json\",\"projects\":[],\"materials\":[\"global.json\"]}");
        var manifestPath = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckManifestPath);
        var manifest = JsonNode.Parse(File.ReadAllText(manifestPath))!;
        manifest["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["materials"] = new JsonArray(Input);
        manifest["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-001")!["report_inputs"] = JsonNode.Parse("[{\"producer\":\"Meta/ReportProducers/check.json\",\"consumer\":\"Meta/ReportConsumers/check.json\",\"artifact\":\"raw-lean-report\",\"materials\":[\"global.json\"]}]");
        File.WriteAllText(manifestPath, manifest.ToJsonString());
        fixture.CommitPlan();
        fixture.Processes();
        fixture.Report();
        return fixture;
    }

    private static CheckUnitResult RunSelectedWithoutOriginalMaterials(ResourceRouteTests.ResourceFixture fixture)
    {
        // A new runner has only the restored seed. Unselected original materials
        // and the canonical report must not be required by the selected export.
        var unselected = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"))
            .Units.Where(unit => unit.Id != "filemap").SelectMany(unit => unit.Materials).Select(material => material.Path).ToHashSet(StringComparer.Ordinal);
        Directory.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "check-material"), recursive: true);
        foreach (var path in CommonExecutionEvidence.ReportPaths) File.Delete(Path.Combine(fixture.Root, path));
        using var selectedOutput = new StringWriter();
        Assert.True(fixture.Run("current", selectedOutput) == 0, selectedOutput.ToString());
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Equal("filemap", Assert.Single(current.Steps).Name);
        Assert.DoesNotContain(current.Materials, material => CommonExecutionEvidence.ReportPaths.Contains(material.Path));
        Assert.DoesNotContain(current.Materials, material => unselected.Contains(material.Path));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)));
        var selected = Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root,
            CommonExecutionEvidence.ChecksPath("current")).Units);
        Assert.Equal("filemap", selected.Id);
        fixture.Report();
        return selected;
    }

    private static CommonCheckRecord FullCurrent(ResourceRouteTests.ResourceFixture fixture, List<string> calls)
    {
        calls.Clear();
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        var checks = CommonExecutionEvidence.BeginChecks(fixture.Root, "current", build, TextWriter.Null);
        foreach (var id in checks.Ids) checks.Run(id, () =>
        {
            calls.Add(id);
            return new([new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal)
                ? CommonCheckRegistrationFixture.Predicate(id) : "passed")],
                id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null);
        });
        var record = checks.Seal();
        CommonExecutionEvidence.SealCurrent(fixture.Root, build,
            CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/log")).ToArray());
        return record;
    }
}
