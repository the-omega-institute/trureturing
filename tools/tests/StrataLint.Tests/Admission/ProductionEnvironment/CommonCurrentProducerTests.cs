using System.Collections.Immutable;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.Scribe;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class CommonCurrentProducerTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ActualScribeCapabilityFeedsCurrentOwnerAndWarmPredicatesDoNotExecute(bool selected)
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Golden/Projection/statement-projection-pilot-v1.json"] = "{\"schema\":\"statement-projection-pilot-fixture-v1\",\"declarations\":[{\"source_path\":\"D5/S0/Carrier/Ring.lean\",\"name\":\"goldenRing\",\"kind\":\"def\",\"type\":\"Nat\"}]}";
        fixture.Files["Golden/Projection/statement-projection-expansion-v1.json"] = "{\"schema\":\"statement-projection-expansion-fixture-v1\",\"declarations\":[]}";
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        var checksDeclaration = JsonNode.Parse(fixture.Files["Meta/ci-checks.json"])!;
        checksDeclaration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "SL-001")!["report_inputs"] = JsonNode.Parse("[{\"producer\":\"Meta/ReportProducers/lean-report.json\",\"artifact\":\"raw-lean-report\",\"materials\":[\"global.json\"]}]");
        foreach (var id in new[] { "SL-006", "SL-023", "SL-025", "scribe-describe" })
        {
            var inputs = new JsonArray();
            if (id == "SL-006") inputs.Add(JsonNode.Parse("{\"producer\":\"Meta/ReportProducers/lean-report.json\",\"artifact\":\"raw-lean-report\",\"materials\":[\"global.json\"]}"));
            inputs.Add(JsonNode.Parse("{\"producer\":\"Meta/ReportProducers/scribe-content.json\",\"artifact\":\"" + (id == "scribe-describe" ? "raw-lean-report" : "VerifiedScribeEmissions") + "\",\"materials\":[\"global.json\"]}"));
            checksDeclaration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == id)!["report_inputs"] = inputs;
        }
        fixture.Files["Meta/ci-checks.json"] = checksDeclaration.ToJsonString();
        fixture.Files["Meta/ReportProducers/lean-report.json"] = "{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"materials\":[\"global.json\"]}";
        fixture.Files["Meta/ReportProducers/scribe-content.json"] = "{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[\"tools/StrataLint.Scribe/StrataLint.Scribe.csproj\"],\"materials\":[\"global.json\"]}";
        fixture.Files["Meta/registry.yaml"] = fixture.Files["Meta/registry.yaml"].Replace("  - \"Meta/ci-checks.json\"", "  - \"Meta/ReportProducers/lean-report.json\"\n  - \"Meta/ci-checks.json\"", StringComparison.Ordinal);
        fixture.Files["Meta/registry.yaml"] = fixture.Files["Meta/registry.yaml"].Replace("  - \"Meta/ci-checks.json\"", "  - \"Meta/ReportProducers/scribe-content.json\"\n  - \"Meta/ci-checks.json\"", StringComparison.Ordinal);
        fixture.Files["global.json"] = "{\"sdk\":{\"version\":\"10.0.103\"}}";
        foreach (var file in fixture.Files)
        {
            var destination = Path.Combine(root, file.Key);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, file.Value);
        }
        File.WriteAllText(Path.Combine(root, ".gitignore"), "build/\n.lake/\n");
        Git("init", "-q"); Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "current producer");
        var data = fixture.BuildForRuleCompatibility();
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            System.Text.Encoding.UTF8.GetBytes(fixture.Files["Meta/registry.yaml"]),
            System.Text.Encoding.UTF8.GetBytes(fixture.Files["Meta/domains.yaml"]))).Policy;
        var report = LeanAxiomReport.Create(fixture.Reports);
        var rawPath = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        RawLeanReportArtifact.WriteFile(rawPath, CommonExecutionEvidence.Snapshot(root), report);
        foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" }) File.WriteAllText(rawPath + suffix, "fixture companion\n");
        const string log = "build/ci/producer.log";
        Directory.CreateDirectory(Path.Combine(root, "build/ci"));
        File.WriteAllText(Path.Combine(root, log), "build\n");
        var definition = DocumentDefinition.Create(ScribeDocument.Create(
            DefinitionDsl.Header("D5/S0/Carrier/Ring", "Current producer fixture."), DefinitionDsl.H("Ring"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Current producer body.")))), RuleFixture.BlueprintSourcePath);
        var emitted = 0;
        for (var cycle = 0; cycle < 3; cycle++)
        {
            var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), [log],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
            var checks = CommonExecutionEvidence.BeginChecks(root, "current", build, TextWriter.Null, selected ? ["SL-006", "scribe-describe"] : null);
            if (!selected) checks.Run("scribe-projections", () =>
            {
                using var error = new StringWriter();
                var findings = StatementProjectionReconciliation.Check(root, DeclarationCatalog.Create(report));
                return new([new("scribe-projections", findings.IsEmpty ? 0 : 1, string.Join("\n", findings))]);
            });
            checks.Run("scribe-describe", () =>
            {
                emitted++;
                using var error = new StringWriter();
                var capability = ProductionScribeEmissionVerifier.VerifyMaterialized(typeof(ScribeCli).Assembly, root, report, null, null, [definition]);
                Assert.True(capability is not null, error.ToString());
                return new([new("scribe-describe", 0, "actual producer verified")], capability.WriteMaterial());
            });
            // This fixture targets the capability/predicate boundary; independent filemap
            // and markdown producer behavior is covered by their native command suites.
            foreach (var id in selected ? Array.Empty<string>() : new[] { "filemap", "scribe-markdown" }) checks.Run(id, () => new([new(id, 0, "fixture boundary")]));
            var result = Assert.IsType<RuleExecutionOutcome.Completed>(checks.ExecuteCurrentPredicates(policy, data.Lean)).Capability;
            Assert.DoesNotContain(result.Diagnostics, d => d.AdmissionEffect != AdmissionEffect.Observe);
            Assert.Equal(cycle == 0 ? selected ? 1 : 18 : 0, result.ExecutedRules.Length);
            var record = checks.Seal();
            foreach (var id in selected ? new[] { "SL-006" } : new[] { "SL-006", "SL-023", "SL-025" })
            {
                var predicate = record.Units.Single(unit => unit.Id == id);
                Assert.NotNull(predicate.Data);
                var bound = VerifiedScribeEmissions.ReadMaterial(File.ReadAllText(Path.Combine(root, predicate.Data)), CommonExecutionEvidence.Snapshot(root));
                Assert.True(bound.TryGet("D5/S0/Carrier/Ring", out _));
            }
            if (selected)
            {
                // Exercise optional selected reuse with the original material paths and provenance.
                var seedRoot = Path.Combine(root, CommonExecutionEvidence.CheckSeedPath("current"));
                Directory.CreateDirectory(seedRoot);
                foreach (var material in record.Units.SelectMany(unit => unit.Materials).Distinct())
                {
                    var target = Path.Combine(seedRoot, material.Path);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(Path.Combine(root, material.Path), target, true);
                }
                CommonExecutionEvidence.Write(seedRoot, "checks.json", record);
                continue;
            }
            CommonExecutionEvidence.SealCurrent(root, build, CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
            Assert.True(CommonExecutionEvidence.ExportCheckSeed(root, "current", TextWriter.Null));
        }
        Assert.Equal(1, emitted);
        // A producer may produce different validated semantics with identical source
        // bytes. Current reuse binds the report value as well as declared source inputs.
        var changedReports = fixture.Reports.ToDictionary(pair => pair.Key, pair => pair.Value);
        changedReports[RuleFixture.RingPath] = new LeanFileReport([], [new LeanDeclaration("goldenRing", "def", "Nat", ["Classical.choice"])]);
        RawLeanReportArtifact.WriteFile(rawPath, CommonExecutionEvidence.Snapshot(root), LeanAxiomReport.Create(changedReports));
        var selection = CommonExecutionEvidence.BeginChecks(root, "current", CommonExecutionEvidence.ValidateBuild(root), TextWriter.Null, selected ? ["SL-006", "scribe-describe"] : null);
        Assert.Equal(selected ? new[] { "SL-006", "scribe-describe" } : new[] { "SL-001", "SL-006", "SL-023", "SL-025", "scribe-describe" }, selection.Ids.Where(selection.IsSelected));
        void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
        }
    }
}
