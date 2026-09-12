using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class RegisteredAdmissionResourcesTests(ITestOutputHelper output, RegisteredAdmissionResourcesTests.RegisteredBase basis)
    : IClassFixture<RegisteredAdmissionResourcesTests.RegisteredBase>
{
    [Theory]
    [InlineData("Meta/ci-checks.json", false)]
    [InlineData("Meta/ci-checks.json", true)]
    [InlineData("Meta/ReportProducers/scribe-content.json", false)]
    [InlineData("Meta/ReportProducers/scribe-content.json", true)]
    [InlineData("Meta/judge-seed.json", false)]
    [InlineData("Meta/judge-seed.json", true)]
    [InlineData("Meta/package-materials.json", false)]
    [InlineData("Meta/package-materials.json", true)]
    [InlineData("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", false)]
    [InlineData("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", true)]
    [InlineData("tools/tests/CompileFailProof/MissingCapability.cs", false)]
    [InlineData("tools/tests/CompileFailProof/MissingCapability.cs", true)]
    [InlineData("tools/tests/JudgeSeedTask.Tests/JudgeSeedInputsTests.cs", false)]
    [InlineData("tools/tests/JudgeSeedTask.Tests/JudgeSeedInputsTests.cs", true)]
    [InlineData("tools/tests/StrataLint.EngineeringScope.Tests/ResourceAdapterTests.cs", false)]
    [InlineData("tools/tests/StrataLint.EngineeringScope.Tests/ResourceAdapterTests.cs", true)]
    [InlineData("tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj", false)]
    [InlineData("tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj", true)]
    [InlineData("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json", false)]
    [InlineData("tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json", true)]
    [InlineData("tools/tests/StrataLint.Tests/Fixtures/admission-resource-probe.trx", false)]
    [InlineData("tools/tests/StrataLint.Tests/Fixtures/admission-resource-probe.trx", true)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py", false)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py", true)]
    [InlineData("tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml", false)]
    [InlineData("tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml", true)]
    [InlineData("tools/tests/Trureturing.Truth.Tests/AdmissionResourceProbe.cs", false)]
    [InlineData("tools/tests/Trureturing.Truth.Tests/AdmissionResourceProbe.cs", true)]
    public void RegisteredJudgeChangesKeepDeltaReachableWithOrWithoutNoResourceContent(string judge, bool mixed)
    {
        var plan = Plan(judge, mixed ? "docs/reports/ci-fixture-plane-probe.md" : "");
        Assert.Equal("required", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        Assert.Equal(new[] { "build", "current", "delta", "engineering", "filemap", "lean", "lean-report", "scribe" },
            Strings(plan["resources"]!));
        Assert.Equal(new[] { "build", "engineering", "current", "delta" }, Strings(plan["selected_stages"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Contains(judge, plan["paths"]!.AsArray().Select(row => row!["path"]!.GetValue<string>()));
        Assert.Equal(mixed ? 2 : 1, plan["paths"]!.AsArray().Count);
        if (mixed)
            Assert.Empty(plan["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>().StartsWith("docs/reports/", StringComparison.Ordinal))!["require"]!.AsArray());
    }

    [Theory]
    [InlineData("README.md")]
    [InlineData("docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md")]
    [InlineData("docs/develop/spec/trureturing_engineering_optimization_v1.md")]
    [InlineData("docs/reports/ci-fixture-plane-probe.md")]
    public void RegisteredContentAloneStillNeedsNoResources(string content)
    {
        var plan = Plan("", content);
        foreach (var field in new[] { "resources", "selected_stages", "tools", "cache_layers" })
            Assert.Empty(plan[field]!.AsArray());
        foreach (var stage in new[] { "build", "engineering", "current", "delta" })
            Assert.Equal("not-required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        foreach (var field in new[] { "projects", "checks", "steps" })
            Assert.Empty(plan["execution"]![field]!.AsArray());
    }

    private JsonNode Plan(string judge, string content)
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
            ci_plan.write(changes, ci_plan.pr_paths(root, merge, base, head))
            print(merge)
            """, basis.Path, basis.Commit, judge, content);
        Assert.True(prepared.Exit == 0, prepared.Text);
        var result = Python(temporary.Path, """
            import json, pathlib, sys
            source, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            print(json.dumps(ci_plan.make_plan(root, sys.argv[3], root / 'build/ci/changes.json')))
            """, prepared.Text.Trim());
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
                manifest = ci_plan.load_filemap((source / ci_plan.FILEMAP).read_bytes())
                # Only explicitly registered planning inputs populate the immutable base.
                materials = {ci_plan.FILEMAP}
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
