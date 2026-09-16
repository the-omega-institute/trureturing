using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class CurrentSeedCoverageTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedCurrentSnapshotPreservesPreviouslyAcceptedUnselectedUnits(bool selectedInputChanges)
    {
        using var fixture = Prepare();
        var calls = new List<string>();
        var original = FullCurrent(fixture, calls);
        Assert.Equal(21, calls.Count);
        Assert.NotNull(original.Units.Single(unit => unit.Id == "SL-001").Report);
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
        Assert.Equal(21, CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "current").Units.Length);

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
        Assert.Equal(21, final.Units.Length);
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
        Assert.Equal(20, calls.Count);
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
        Assert.Equal(21, exported.Units.Length);
    }

    private const string Input = "fixtures/filemap-input.txt";

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
