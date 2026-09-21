using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class RegisteredAdmissionResourcesTests(ITestOutputHelper output, RegisteredAdmissionResourcesTests.RegisteredBase basis)
    : IClassFixture<RegisteredAdmissionResourcesTests.RegisteredBase>
{
    private const string RegisteredNoResourceContent = "docs/reports/prime-slab-corner-order-0909.json";

    [Theory]
    [InlineData("Meta/domains.yaml", "push")]
    [InlineData("Meta/domains.yaml", "pr")]
    [InlineData("Meta/registry.yaml", "push")]
    [InlineData("Meta/registry.yaml", "pr")]
    public void RegistryDataRunsRegisteredConsumersAndRetainsCurrentTruthChecks(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.Equal(mode == "pr", Strings(plan["resources"]!).Contains("current"));
        Assert.Contains("scribe", Strings(plan["resources"]!));
        Assert.Equal(mode == "push" ? new[] { "lean-report", "scribe", "filemap" }
            : ["lean-report", "scribe", "filemap", "check-current"], Strings(plan["execution"]!["steps"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/scripts/agent/merge-gate.sh", "push")]
    [InlineData("tools/scripts/agent/merge-gate.sh", "pr")]
    [InlineData("tools/scripts/agent/openproblem/erdos617.py", "push")]
    [InlineData("tools/scripts/agent/openproblem/erdos617.py", "pr")]
    [InlineData("tools/scripts/agent/openproblem/standing-check.py", "push")]
    [InlineData("tools/scripts/agent/openproblem/standing-check.py", "pr")]
    public void AgentScriptsRunRegisteredConsumersWithoutCurrentTruthChecks(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.Empty(plan["execution"]!["lean_targets"]!.AsArray());
        Assert.Equal(mode == "push" ? new[] { "filemap" } : ["SL-003", "SL-015", "SL-019", "filemap"],
            Strings(plan["execution"]!["checks"]!));
        Assert.Equal(mode == "push" ? new[] { "filemap" }
            : ["lean-report", "filemap", "check-current"], Strings(plan["execution"]!["steps"]!));
        Assert.Equal(mode == "push" ? "not-applicable" : "required",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        foreach (var unrelated in new[] { "engineering", "current", "scribe", "lean-inspector-build" })
            Assert.DoesNotContain(unrelated, Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/lean-inspector/tests/test_reuse.py")]
    [InlineData("tools/scripts/agent/openproblem/erdos617.py")]
    public void FileMapOnlyPushPlansKeepBuildAndTestCachesWithoutCurrentOrLeanCaches(string input)
    {
        var plan = Plan(input, "", "push");
        var resources = Strings(plan["resources"]!);
        var caches = Strings(plan["cache_layers"]!);

        Assert.Contains("build", resources);
        Assert.Contains("filemap", resources);
        Assert.DoesNotContain("current", resources);
        Assert.DoesNotContain("lean", resources);
        Assert.DoesNotContain("lean-report", resources);
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.DoesNotContain("current", caches);
        Assert.DoesNotContain("dependency", caches);
        Assert.DoesNotContain("project", caches);
        Assert.Contains("judge", caches);
        Assert.Contains("engineering", caches);
        Assert.Contains("elan", caches);
    }

    [Fact]
    public void DeltaJudgeReportPlanRetainsCurrentReportSeedThroughLeanReport()
    {
        var plan = Plan("docs/develop/spec/golden-ledger-repo-spec.md", "", "pr");
        var resources = Strings(plan["resources"]!);
        var caches = Strings(plan["cache_layers"]!);

        Assert.Equal(new[] { "build", "delta-judge", "filemap", "lean", "lean-report" }, resources);
        Assert.Equal(new[] { "lean-report", "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.DoesNotContain("current", resources);
        Assert.Contains("current", caches);
    }

    [Theory]
    [InlineData("tools/scripts/preflight.sh", "push")]
    [InlineData("tools/scripts/preflight.sh", "pr")]
    [InlineData("tools/scripts/lib/admission-base-lib.sh", "push")]
    [InlineData("tools/scripts/lib/admission-base-lib.sh", "pr")]
    [InlineData("tools/scripts/report/lean-report-selection.py", "push")]
    [InlineData("tools/scripts/report/lean-report-selection.py", "pr")]
    [InlineData("tools/scripts/workflow/ci_plan.py", "push")]
    [InlineData("tools/scripts/workflow/ci_plan.py", "pr")]
    [InlineData("tools/scripts/worktree/lean_cache.py", "push")]
    [InlineData("tools/scripts/worktree/lean_cache.py", "pr")]
    public void CommonBuildAndWorkflowProgramsRetainTheirRegisteredChecks(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Contains("engineering", Strings(plan["resources"]!));
        Assert.Equal(10, plan["execution"]!["tests"]!.AsArray().Count);
        Assert.Equal(mode == "push" ? new[] { "lean-report", "scribe", "filemap" }
            : ["lean-report", "scribe", "filemap", "check-current"], Strings(plan["execution"]!["steps"]!));
    }

    [Theory]
    [InlineData("tools/lean-inspector/tests/test_native_support.py", "push")]
    [InlineData("tools/lean-inspector/tests/test_native_support.py", "pr")]
    [InlineData("tools/lean-inspector/tests/test_reuse.py", "push")]
    [InlineData("tools/lean-inspector/tests/test_reuse.py", "pr")]
    public void InspectorTestFixturesRunRegisteredTestConsumersWithoutCurrentTruthChecks(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.Empty(plan["execution"]!["lean_targets"]!.AsArray());
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal(mode == "push" ? new[] { "filemap" } : ["lean-report", "filemap"],
            Strings(plan["execution"]!["steps"]!));
        Assert.Equal(mode == "push" ? "not-applicable" : "required",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        foreach (var unrelated in new[] { "engineering", "current", "scribe", "lean-inspector-build" })
            Assert.DoesNotContain(unrelated, Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/lean-inspector/native.py", "push")]
    [InlineData("tools/lean-inspector/native.py", "pr")]
    [InlineData("tools/lean-inspector/Census/native.py", "push")]
    [InlineData("tools/lean-inspector/Census/native.py", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/RegistrationGates/MutationMatrix.py", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/RegistrationGates/MutationMatrix.py", "pr")]
    public void OtherInspectorPythonProgramsKeepRegisteredCurrentChecks(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Contains("engineering", Strings(plan["resources"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            Strings(plan["execution"]!["steps"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void InspectorSourceRunsOnlyRegisteredConsumers(string mode)
    {
        var plan = Plan("tools/lean-inspector/Inspector.lean", "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
            "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        AssertInspectorSourceObligations(plan, mode);
    }

    [Theory]
    [InlineData("tools/lean-inspector/LeanInformationAudit/NameWire.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/NameWire.lean", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "pr")]
    public void AuditLeanSourcesRunOnlyRegisteredConsumers(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        AssertInspectorSourceObligations(plan, mode);
    }

    private static void AssertInspectorSourceObligations(JsonNode plan, string mode)
    {
        var resources = Strings(plan["resources"]!);
        foreach (var required in new[] { "current", "filemap", "lean-inspector-build", "lean-report", "scribe" })
        {
            Assert.Contains(required, Strings(plan["declared_require"]!));
            Assert.Contains(required, resources);
        }
        Assert.Contains("delta", Strings(plan["declared_require"]!));
        Assert.Equal(mode == "pr", resources.Contains("delta"));
        Assert.DoesNotContain("engineering", resources);
        Assert.DoesNotContain("engineering-guards", resources);
        Assert.Equal(CommonCheckRegistrationFixture.Ids
            .Where(id => !CommonExecutionEvidence.EngineeringCheckIds.Contains(id)).Order(StringComparer.Ordinal),
            Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "LeanInformationAudit", "leanInspector/reportInspector" },
            Strings(plan["execution"]!["lean_targets"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            Strings(plan["execution"]!["steps"]!));
        foreach (var stage in new[] { "build", "engineering", "current" })
            Assert.Equal("required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        Assert.Equal(mode == "pr" ? "required" : "not-applicable",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void CachePathChangesRunOnlyRegisteredCacheConsumers(string mode)
    {
        var plan = Plan("Meta/ci-cache-paths.json", "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj",
            "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.Empty(plan["execution"]!["lean_targets"]!.AsArray());
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal(mode == "push" ? new[] { "filemap" } : ["lean-report", "filemap"],
            Strings(plan["execution"]!["steps"]!));
        Assert.Equal(mode == "push" ? "not-applicable" : "required",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/lean-inspector/Inspector.lean", "push")]
    [InlineData("tools/lean-inspector/Inspector.lean", "pr")]
    [InlineData("tools/lean-inspector/native_image.c", "push")]
    [InlineData("tools/lean-inspector/native_image.c", "pr")]
    [InlineData("tools/lean-inspector/lakefile.lean", "push")]
    [InlineData("tools/lean-inspector/lakefile.lean", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Tests/Projection/AnalysisContract.lean", "pr")]
    public void RegisteredInspectorProgramsAndTestsRequireCompilationWithoutAnotherReportStep(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.Contains("lean-inspector-build", Strings(plan["resources"]!));
        Assert.Equal(new[] { "LeanInformationAudit", "leanInspector/reportInspector" },
            Strings(plan["execution"]!["lean_targets"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            Strings(plan["execution"]!["steps"]!));
    }

    [Theory]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean", "push")]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean", "pr")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json", "push")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json", "pr")]
    [InlineData("tools/lean-inspector/LeanInformationAuditAnalysis/Tests/WitnessCarriers.lean", "push")]
    [InlineData("tools/lean-inspector/LeanInformationAuditAnalysis/Tests/WitnessCarriers.lean", "pr")]
    [InlineData("tools/lean-inspector/Census/config.lean", "push")]
    [InlineData("tools/lean-inspector/Census/config.lean", "pr")]
    public void RegisteredContentAndMetadataDoNotRequireInspectorProgramCompilation(string input, string mode)
    {
        var plan = Plan(input, "", mode);
        Assert.DoesNotContain("lean-inspector-build", Strings(plan["resources"]!));
        Assert.Empty(plan["execution"]!["lean_targets"]!.AsArray());
    }

    [Theory]
    [InlineData("Meta/ci-checks.json", false)]
    [InlineData("Meta/ci-checks.json", true)]
    [InlineData("Meta/ReportProducers/scribe-content.json", false)]
    [InlineData("Meta/ReportProducers/scribe-content.json", true)]
    [InlineData("Meta/judge-seed.json", false)]
    [InlineData("Meta/judge-seed.json", true)]
    [InlineData("Meta/package-materials.json", false)]
    [InlineData("Meta/package-materials.json", true)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py", false)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py", true)]
    [InlineData("tools/scripts/preflight.sh", false)]
    [InlineData("tools/scripts/agent/openproblem/TARGET-GATES.md", false)]
    public void RegisteredJudgeChangesKeepDeltaReachableWithOrWithoutNoResourceContent(string judge, bool mixed)
    {
        var plan = Plan(judge, mixed ? RegisteredNoResourceContent : "");
        Assert.Equal("required", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        Assert.Equal(new[] { "build", "current", "delta", "engineering", "filemap", "lean", "lean-report", "scribe" },
            Strings(plan["resources"]!));
        Assert.Equal(new[] { "build", "engineering", "current", "delta" }, Strings(plan["selected_stages"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Contains(judge, plan["paths"]!.AsArray().Select(row => row!["path"]!.GetValue<string>()));
        Assert.Equal(mixed ? 2 : 1, plan["paths"]!.AsArray().Count);
        if (mixed)
            Assert.Empty(plan["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == RegisteredNoResourceContent)!["require"]!.AsArray());
    }

    [Theory]
    [InlineData("README.md")]
    [InlineData("docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md")]
    [InlineData("docs/develop/spec/trureturing_engineering_optimization_v1.md")]
    [InlineData(RegisteredNoResourceContent)]
    [InlineData("docs/reports/ci-fixture-plane-probe.md")]
    [InlineData("tools/scripts/agent/openproblem/README.md")]
    [InlineData("tools/scripts/agent/openproblem/SCREENED-OUT.md")]
    public void RegisteredFilesAloneStillNeedNoResources(string content)
    {
        var plan = Plan("", content);
        foreach (var field in new[] { "resources", "selected_stages", "tools", "cache_layers" })
            Assert.Empty(plan[field]!.AsArray());
        foreach (var stage in new[] { "build", "engineering", "current", "delta" })
            Assert.Equal("not-required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        foreach (var field in new[] { "projects", "checks", "steps", "lean_targets" })
            Assert.Empty(plan["execution"]![field]!.AsArray());
    }

    [Theory]
    [InlineData("push", false)]
    [InlineData("push", true)]
    [InlineData("pr", false)]
    [InlineData("pr", true)]
    public void ReviewTemplateChangesRetainAdmissionWithoutEngineering(string mode, bool mixed)
    {
        var template = "tools/scripts/agent/openproblem/templates/"
            + (mixed ? "judgement-form-check-template.md" : "mirror-check-template.md");
        AssertJudgeDocumentResources(template, mode, mixed);
    }

    [Theory]
    [InlineData("CLAUDE.md", "push")]
    [InlineData("CLAUDE.md", "pr")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md", "push")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md", "pr")]
    public void PolicyDocumentsRetainAdmissionWithoutEngineering(string document, string mode) =>
        AssertJudgeDocumentResources(document, mode, mixed: false);

    [Theory]
    [InlineData("CLAUDE.md")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md")]
    public void PolicyDocumentsDoNotExpandRegisteredProductionConsumers(string document)
    {
        var plan = Plan("tools/StrataLint.Engine/Rules/CapacityRule.cs", document);
        var tests = Strings(plan["execution"]!["tests"]!);
        Assert.Equal(9, tests.Length);
        Assert.Contains("tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj", tests);
        Assert.DoesNotContain("tools/tests/Trureturing.Truth.Tests/Trureturing.Truth.Tests.csproj", tests);
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.Equal("required", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
    }

    private void AssertJudgeDocumentResources(string document, string mode, bool mixed)
    {
        var plan = Plan(document, mixed ? RegisteredNoResourceContent : "", mode);
        Assert.Equal(new[] { "delta-judge", "filemap" }, Strings(plan["declared_require"]!));
        Assert.Empty(plan["execution"]!["tests"]!.AsArray());
        Assert.Empty(plan["execution"]!["lean_targets"]!.AsArray());
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
        Assert.DoesNotContain("engineering", Strings(plan["cache_layers"]!));
        Assert.Equal(mixed ? 2 : 1, plan["paths"]!.AsArray().Count);
        if (mode == "push")
        {
            Assert.Equal(new[] { "build", "filemap" }, Strings(plan["resources"]!));
            Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["steps"]!));
            Assert.Equal(new[] { "judge" }, Strings(plan["cache_layers"]!));
            Assert.Equal("not-applicable", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        }
        else
        {
            Assert.Equal(new[] { "build", "delta-judge", "filemap", "lean", "lean-report" },
                Strings(plan["resources"]!));
            Assert.Equal(new[] { "lean-report", "filemap" }, Strings(plan["execution"]!["steps"]!));
            Assert.Equal("required", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        }
    }

    [Theory]
    [InlineData("Meta/Digestion/atoms/sha256/admission-resource-probe", "push")]
    [InlineData("Meta/Digestion/atoms/sha256/admission-resource-probe", "pr")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json", "push")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json", "pr")]
    public void RegisteredDigestionMetadataKeepsDeltaReportWithoutUnrelatedCurrentChecks(string metadata, string mode)
    {
        const string theory = "docs/develop/theory/admission-resource-probe.md";
        var plan = Plan(metadata, theory, mode);
        Assert.Equal(new[] { "current-metadata", "delta-metadata", "filemap" }, Strings(plan["declared_require"]!));
        Assert.Empty(Strings(plan["paths"]!.AsArray()
            .Single(row => row!["path"]!.GetValue<string>() == theory)!["require"]!));
        if (mode == "push")
        {
            Assert.Equal(new[] { "build", "current-metadata", "filemap" }, Strings(plan["resources"]!));
            Assert.Equal(new[] { "build", "current" }, Strings(plan["selected_stages"]!));
            Assert.Equal(new[] { "bash", "dotnet", "git", "python3" }, Strings(plan["tools"]!));
            Assert.Equal(new[] { "current", "judge" }, Strings(plan["cache_layers"]!));
            Assert.Equal(new[] { "tools/StrataLint.Cli/StrataLint.Cli.csproj" }, Strings(plan["execution"]!["projects"]!));
            Assert.Equal(new[] { "SL-003", "SL-015", "SL-019", "filemap" }, Strings(plan["execution"]!["checks"]!));
            Assert.Equal(new[] { "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
            Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.Equal("not-applicable", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        }
        else
        {
            Assert.Equal(new[] { "build", "current-metadata", "delta-metadata", "filemap", "lean", "lean-report" },
                Strings(plan["resources"]!));
            Assert.Equal(new[] { "build", "current", "delta" }, Strings(plan["selected_stages"]!));
            Assert.Empty(plan["execution"]!["tests"]!.AsArray());
            Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.Equal(new[] { "lean-report", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
            Assert.Equal(new[] { "SL-003", "SL-015", "SL-019", "filemap" },
                Strings(plan["execution"]!["checks"]!));
            Assert.Equal("required", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        }
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void TheoryDocumentsNeedNoBuildChecksOrCaches(string mode)
    {
        var plan = Plan("", "docs/develop/theory/admission-resource-probe.md", mode);
        foreach (var field in new[] { "resources", "selected_stages", "tools", "cache_layers" })
            Assert.Empty(plan[field]!.AsArray());
        foreach (var field in new[] { "projects", "checks", "steps" })
            Assert.Empty(plan["execution"]![field]!.AsArray());
    }

    [Theory]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Golden/Frozen/state/D5/F/NumberTheory/AdmissionResourceProbe.lean.json")]
    [InlineData("Meta/ci-checks.json")]
    [InlineData("Meta/registry.yaml")]
    public void TheoryDocumentsDoNotRemoveOtherInputsRequirements(string input)
    {
        var plan = Plan(input, "docs/develop/theory/admission-resource-probe.md");
        Assert.Equal(input is "Meta/ci-checks.json", Strings(plan["resources"]!).Contains("engineering"));
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Contains("delta", Strings(plan["resources"]!));
        Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => input is "Meta/ci-checks.json"
                || !CommonExecutionEvidence.EngineeringCheckIds.Contains(id)).Order(StringComparer.Ordinal),
            Strings(plan["execution"]!["checks"]!));
    }

    [Theory]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Golden/Frozen/state/D5/F/NumberTheory/AdmissionResourceProbe.lean.json")]
    [InlineData("Meta/ci-checks.json")]
    [InlineData("Meta/registry.yaml")]
    public void AdditionalSemanticOrJudgeInputRetainsItsFullRegisteredRequirements(string input)
    {
        var plan = Plan("Meta/Digestion/backfill/admission-resource-probe.json", input);
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Contains("delta", Strings(plan["resources"]!));
        Assert.Contains("scribe", Strings(plan["resources"]!));
        Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => input is "Meta/ci-checks.json"
            || !CommonExecutionEvidence.EngineeringCheckIds.Contains(id)).Order(StringComparer.Ordinal), Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
    }

    [Theory]
    [InlineData("JudgeSeedTask.Tests", "JudgeSeedInputsTests.cs", "test-judge-seed")]
    [InlineData("StrataLint.ArchitectureTests", "ArchitectureTests.cs", "architecture")]
    [InlineData("StrataLint.EngineeringScope.Tests", "ResourceAdapterTests.cs", "test-engineering-scope")]
    [InlineData("StrataLint.EngineeringScope.Tests", "StrataLint.EngineeringScope.Tests.csproj", "test-engineering-scope")]
    [InlineData("StrataLint.Tests", "Commands/FileMapPlanning/canonical.json", "test-cli")]
    [InlineData("StrataLint.EngineeringScope.Tests", "Fixtures/infrastructure-skip.trx", "test-engineering-scope")]
    [InlineData("StrataLint.Tests", "Fixtures/fixture-registry.yaml", "test-cli")]
    [InlineData("StrataLint.Engine.Tests", "RegressionTests.cs", "test-engine")]
    [InlineData("StrataLint.Lean.Tests", "Native/InspectorNativeTests.cs", "test-lean")]
    [InlineData("StrataLint.Cache.Tests", "LeanCachePublishTests.cs", "test-cache")]
    [InlineData("StrataLint.Scribe.Tests", "FileMap/ResourceTests.cs", "test-scribe")]
    [InlineData("Trureturing.Truth.Tests", "AdmissionResourceProbe.cs", "test-truth")]
    public void TestChangesSelectTheirRegisteredProjectWithoutUnrelatedTestExecution(string project, string file, string resource)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan($"tools/tests/{project}/{file}", "", mode);
            var architecture = file.EndsWith(".cs", StringComparison.Ordinal) || file.EndsWith(".csproj", StringComparison.Ordinal);
            Assert.Equal(new[] { $"tools/tests/{project}/{project}.csproj" }
                .Concat(architecture ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj" } : [])
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), Strings(plan["execution"]!["tests"]!));
            Assert.Contains(resource, Strings(plan["resources"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["checks"]!));
            Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.ToString());
            Assert.Equal(mode == "pr" ? new[] { "lean-report", "filemap" } : ["filemap"], Strings(plan["execution"]!["steps"]!));
        }
    }

    [Theory]
    [InlineData("StrataLint.Cli", "StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.Tests")]
    [InlineData("StrataLint.EngineeringScope", "StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.EngineeringScope.Tests,StrataLint.Tests")]
    [InlineData("StrataLint.Lean", "StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.EngineeringScope.Tests,StrataLint.Lean.Tests,StrataLint.Tests")]
    [InlineData("StrataLint.Scribe", "StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.Scribe.Documents.Tests,StrataLint.Scribe.Tests,StrataLint.Tests")]
    [InlineData("StrataLint.Scribe.Documents", "StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.Scribe.Documents.Tests,StrataLint.Tests")]
    [InlineData("StrataLint.Engine", "JudgeSeedTask.Tests,StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.Engine.Tests,StrataLint.EngineeringScope.Tests,StrataLint.Lean.Tests,StrataLint.Scribe.Documents.Tests,StrataLint.Scribe.Tests,StrataLint.Tests")]
    [InlineData("Trureturing.Truth", "JudgeSeedTask.Tests,StrataLint.ArchitectureTests,StrataLint.Cache.Tests,StrataLint.Engine.Tests,StrataLint.EngineeringScope.Tests,StrataLint.Lean.Tests,StrataLint.Scribe.Documents.Tests,StrataLint.Scribe.Tests,StrataLint.Tests,Trureturing.Truth.Tests")]
    public void ProductionProjectsSelectTheirExplicitTestConsumers(string project, string assemblies)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan($"tools/{project}/ResourceRoutingProbe.cs", "", mode);
            Assert.Equal(assemblies.Split(',').Select(name => $"tools/tests/{name}/{name}.csproj"),
                Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            Assert.Contains("engineering-guards", Strings(plan["resources"]!));
            foreach (var guard in new[] { "selftest-pair", "capability-proof", "banned-api-proof" })
                Assert.Contains(guard, Strings(plan["execution"]!["checks"]!));
            Assert.Contains("filemap", Strings(plan["execution"]!["checks"]!));
            Assert.Contains("scribe", Strings(plan["resources"]!));
            Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.ToString());
        }
    }

    [Theory]
    [InlineData("StrataLint.Scribe", "push")]
    [InlineData("StrataLint.Scribe", "pr")]
    [InlineData("StrataLint.Scribe.Documents", "push")]
    [InlineData("StrataLint.Scribe.Documents", "pr")]
    public void ScribeSourceSelectsItsRegisteredCurrentConsumers(string project, string mode)
    {
        var plan = Plan($"tools/{project}/ResourceRoutingProbe.cs", "", mode);
        Assert.Equal(mode == "pr" ? new[] { "SL-006", "SL-023", "SL-025" } : [],
            Strings(plan["execution"]!["checks"]!).Where(id => id.StartsWith("SL-", StringComparison.Ordinal)));
        Assert.DoesNotContain("current", Strings(plan["resources"]!));
        Assert.Equal(mode == "pr", Strings(plan["resources"]!).Contains("current-scribe"));
        Assert.Contains("filemap", Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "scribe-describe", "scribe-markdown", "scribe-projections" },
            Strings(plan["execution"]!["checks"]!).Where(id => id.StartsWith("scribe-", StringComparison.Ordinal)));
        Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.ToString());
    }

    [Fact]
    public void ScribeAndEngineChangesRetainTheFullCurrentRequirement()
    {
        var plan = Plan("tools/StrataLint.Scribe/ResourceRoutingProbe.cs", "tools/StrataLint.Engine/ResourceRoutingProbe.cs");
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal)),
            Strings(plan["execution"]!["checks"]!).Where(id => id.StartsWith("SL-", StringComparison.Ordinal)));
    }

    [Fact]
    public void UnregisteredProductionProjectCannotInheritBlanketEngineering()
    {
        var result = PlanResult("tools/StrataLint.Unregistered/Program.cs", "");
        Assert.NotEqual(0, result.Exit);
        Assert.Contains("FILEMAP match count 0", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("StrataLint.Cli")]
    [InlineData("StrataLint.Scribe")]
    [InlineData("StrataLint.Scribe.Documents")]
    public void ProductionProjectConfigurationAlsoSelectsEngineeringScopeConsumers(string project)
    {
        foreach (var file in new[] { project + ".csproj", "packages.lock.json" })
        {
            var plan = Plan($"tools/{project}/{file}", "");
            Assert.Contains("tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
                Strings(plan["execution"]!["tests"]!));
            Assert.Contains("current", Strings(plan["resources"]!));
            Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal)),
                Strings(plan["execution"]!["checks"]!).Where(id => id.StartsWith("SL-", StringComparison.Ordinal)));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        }
    }

    [Fact]
    public void ProductionAndTestChangesKeepBothRegisteredConsumerSets()
    {
        var plan = Plan("tools/StrataLint.Cli/Program.cs", "tools/tests/StrataLint.Engine.Tests/RegressionTests.cs");
        Assert.Equal(new[] { "StrataLint.ArchitectureTests", "StrataLint.Cache.Tests", "StrataLint.Engine.Tests", "StrataLint.Tests" }
            .Select(name => $"tools/tests/{name}/{name}.csproj"), Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Fact]
    public void SharedTestSupportSelectsItsDeclaredConsumerProjects()
    {
        var plan = Plan("tools/TestSupport/StrataLint.TestSupport/TestBudgets.cs", "");
        Assert.Equal(new[] { "JudgeSeedTask.Tests", "StrataLint.ArchitectureTests", "StrataLint.Cache.Tests",
            "StrataLint.Engine.Tests", "StrataLint.EngineeringScope.Tests", "StrataLint.Lean.Tests", "StrataLint.Scribe.Tests", "StrataLint.Tests" }
            .Select(name => $"tools/tests/{name}/{name}.csproj"), Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs")]
    [InlineData("tools/tests/CompileFailProof/MissingCapability.cs")]
    public void CompileFailureFixturesRequestGuardsAndTheirArchitectureCoverage(string path)
    {
        var plan = Plan(path, "");
        Assert.Equal(new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj" }, Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] { "banned-api-proof", "capability-proof", "filemap", "selftest-pair" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.ToString());
        Assert.Equal(new[] { "lean-report", "filemap" }, Strings(plan["execution"]!["steps"]!));
    }

    private JsonNode Plan(string judge, string content, string mode = "pr")
    {
        var result = PlanResult(judge, content, mode);
        Assert.True(result.Exit == 0, result.Text);
        var plan = JsonNode.Parse(result.Text)!;
        output.WriteLine("REGISTERED_ADMISSION_RESOURCES " + new JsonObject
        {
            ["judge"] = judge, ["content"] = content,
            ["resources"] = plan["resources"]!.DeepClone(),
            ["stages"] = plan["stages"]!.DeepClone(),
            ["cache_layers"] = plan["cache_layers"]!.DeepClone(),
        }.ToJsonString());
        return plan;
    }

    [Fact]
    public void UnregisteredReportContentCannotClaimNoResources()
    {
        var result = PlanResult("", "docs/reports/ci-fixture-plane-probe.unregistered");
        Assert.NotEqual(0, result.Exit);
        Assert.Contains("FILEMAP match count 0", result.Text, StringComparison.Ordinal);
    }

    private (int Exit, string Text) PlanResult(string judge, string content, string mode = "pr")
    {
        using var temporary = new PlanningFixture();
        var prepared = Python(temporary.Path, """
            import json, pathlib, sys
            source, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            def git(*args):
                return ci_plan.git(root, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', *args).decode().strip()
            git('clone', '--quiet', '--no-hardlinks', sys.argv[3], str(root))
            base = git('rev-parse', 'HEAD')
            assert base == sys.argv[4]
            for path in filter(None, sys.argv[5:7]):
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((target.read_bytes() if target.is_file() else b'fixture input\n') + b'\n')
            git('add', '.')
            git('commit', '-qm', 'explicit changed paths')
            head = git('rev-parse', 'HEAD')
            merge = git('commit-tree', git('rev-parse', 'HEAD^{tree}'), '-p', base, '-p', head, '-m', 'candidate')
            git('checkout', '--detach', '-q', merge)
            changes = root / 'build/ci/changes.json'
            scope = ci_plan.push_paths(root, merge, base, merge) if sys.argv[7] == 'push' else ci_plan.pr_paths(root, merge, base, head)
            ci_plan.write(changes, scope)
            print(merge)
            """, basis.Path, basis.Commit, judge, content, mode);
        Assert.True(prepared.Exit == 0, prepared.Text);
        return Python(temporary.Path, """
            import json, pathlib, sys
            source, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            print(json.dumps(ci_plan.make_plan(root, sys.argv[3], root / 'build/ci/changes.json')))
            """, prepared.Text.Trim());
    }

    private static string[] Strings(JsonNode value) => value.AsArray().Select(item => item!.GetValue<string>()).ToArray();

    private static (int Exit, string Text) Python(string root, string code, params string[] arguments) =>
        SharedBuildContractTests.Process(root, "python3", ["-B", "-c", code, TestRepositoryLayout.FindRoot(), root, .. arguments],
            new Dictionary<string, string>
            {
                // Ignore host config and disable automatic maintenance, GC, hooks and fsmonitor.
                ["GIT_CONFIG_NOSYSTEM"] = "1",
                ["GIT_CONFIG_GLOBAL"] = System.IO.Path.Combine(root, "no-global-gitconfig"),
                ["GIT_CONFIG_COUNT"] = "4",
                ["GIT_CONFIG_KEY_0"] = "core.fsmonitor", ["GIT_CONFIG_VALUE_0"] = "false",
                ["GIT_CONFIG_KEY_1"] = "core.hooksPath", ["GIT_CONFIG_VALUE_1"] = System.IO.Path.Combine(root, "no-git-hooks"),
                ["GIT_CONFIG_KEY_2"] = "maintenance.auto", ["GIT_CONFIG_VALUE_2"] = "false",
                ["GIT_CONFIG_KEY_3"] = "gc.auto", ["GIT_CONFIG_VALUE_3"] = "0",
            });

    public sealed class RegisteredBase : IDisposable
    {
        private readonly PlanningFixture directory = new();
        internal string Path => directory.Path;
        internal string Commit { get; }
        public RegisteredBase()
        {
            var result = Python(Path, """
                import pathlib, sys
                source, root = map(pathlib.Path, sys.argv[1:3])
                sys.path.insert(0, str(source / 'tools/scripts/workflow'))
                import ci_plan
                documents = []
                manifest = ci_plan.load_filemap((source / ci_plan.FILEMAP).read_bytes(),
                    lambda path: (source / path).read_bytes(), documents)
                # Only explicitly registered planning inputs populate the immutable base.
                materials = {path for path, _ in documents}
                for row in manifest['resources']:
                    materials.update([row['owner'], *row['materials']])
                for path in sorted(materials):
                    target = root / path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes((source / path).read_bytes())
                (root / '.gitignore').write_text('build/\n')
                def git(*args):
                    return ci_plan.git(root, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', *args).decode().strip()
                git('init', '-q')
                git('add', '.')
                git('commit', '-qm', 'registered base')
                print(git('rev-parse', 'HEAD'))
                """);
            Assert.True(result.Exit == 0, result.Text);
            Commit = result.Text.Trim();
        }
        public void Dispose() => directory.Dispose();
    }

    private sealed class PlanningFixture : IDisposable
    {
        internal string Path { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("admission-resources-").FullName;
        public void Dispose() => TemporaryFileSystem.Directory.Delete(Path, recursive: true);
    }
}
