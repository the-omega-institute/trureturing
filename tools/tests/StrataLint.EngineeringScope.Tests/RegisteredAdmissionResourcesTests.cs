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
    [InlineData("tools/scripts/agent/openproblem/templates/judgement-form-check-template.md", false)]
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
        Assert.Equal(input is "Meta/registry.yaml" or "Meta/ci-checks.json", Strings(plan["resources"]!).Contains("engineering"));
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Contains("delta", Strings(plan["resources"]!));
        Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => input is "Meta/registry.yaml" or "Meta/ci-checks.json"
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
        Assert.Equal(CommonCheckRegistrationFixture.Ids.Where(id => input is "Meta/registry.yaml" or "Meta/ci-checks.json"
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
