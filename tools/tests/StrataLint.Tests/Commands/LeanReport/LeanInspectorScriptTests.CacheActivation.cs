using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class LeanInspectorScriptTests
{
    [Theory]
    [InlineData("cold", true, 0)]
    [InlineData("reuse", false, 0)]
    [InlineData("corrupt", true, 2)]
    [InlineData("missing", true, 2)]
    public void DeferredCacheRouteConsumesTheRealPreparedReport(string scenario, bool build, int exit)
    {
        using var fixture = new RuntimeFixture();
        fixture.Write(".gitignore", "out/\ncache/\nprepared report/\nlake-runs\n.lake/\nbuild/\ntools/**/bin/\ntools/**/obj/\n__pycache__/\n");
        fixture.Write("Meta/FILEMAP.toml", """
            schema_version = 4
            resources = [
              { id = "lean-report", stage = "current", owner = "tools/lean-inspector/inspect.sh", prerequisites = [], tools = [], cache_layers = ["dependency", "project", "report"], cache_activation = {dependency = "lean-production", project = "lean-production", report = "stage-start"}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
            ]
            [residence_policy]
            case_id = "FIXTURE"
            desired = "explicit"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "**"
            require = ["lean-report"]
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["test"]
            verified_by = ["test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n");
        fixture.Write("Meta/ci-resources.json", """
            {"schema":"ci-resource-execution-v1","resources":[{"id":"lean-report","projects":[],"checks":[],"steps":["lean-report"]}]}
            """);
        fixture.Write("Meta/engineering-projects.json", "{\"projects\":[]}");
        fixture.Write("Meta/ci-checks.json", "{\"checks\":[]}");
        Git("init", "--quiet");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "--quiet", "-m", "declared preparation inputs");
        var commit = Git("rev-parse", "HEAD").Trim();
        var repository = TestRepositoryLayout.FindRoot();
        string[] localEnvironment = [.. CiFixtureEnvironment.LocalAssignments, "GITHUB_OUTPUT=", "GITHUB_ENV="];
        var plan = Run("env", [.. localEnvironment, "python3", "-B", Path.Combine(repository, "tools/scripts/workflow/ci.py"),
            "push-plan", "--repository", fixture.Root, "--commit", commit], fixture.Root);
        Assert.True(plan.ExitCode == 0, Encoding.UTF8.GetString(plan.StandardError));
        if (scenario == "reuse") fixture.Pair("full-fallback", 2);
        Assert.Equal("", Git("status", "--porcelain", "--untracked-files=all").Trim());
        var prepared = fixture.Prepare();
        Assert.True(prepared.ExitCode == 0, Encoding.UTF8.GetString(prepared.StandardError));
        Assert.Equal(build, JsonNode.Parse(prepared.StandardOutput)!["needs_lean_build"]!.GetValue<bool>());
        if (scenario == "corrupt") File.WriteAllText(Path.Combine(fixture.Preparation, "delta-plan.json"), "{}");
        if (scenario == "missing") Directory.Delete(fixture.Preparation, true);
        foreach (var command in new[] { "keys", "restore" })
        {
            var result = Run("env", [.. localEnvironment,
                "GITHUB_RUN_ID=17", "GITHUB_RUN_ATTEMPT=2", $"CANDIDATE_SHA={commit}",
                "CI_PLAN_PATH=build/ci/plan.json", "CI_CHANGES_PATH=build/ci/changes.json",
                $"STRATALINT_LEAN_REPORT_PREPARATION={fixture.Preparation}",
                "python3", "-B", Path.Combine(repository, "tools/scripts/worktree/lean_actions.py"), command,
                "--repository", fixture.Root, "--stage", "current", "--phase", "lean-production"], fixture.Root);
            var text = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
            Assert.True(result.ExitCode == exit, text);
            if (exit == 2) Assert.Contains("CI_INPUT_FAILED", text, StringComparison.Ordinal);
            else if (command == "keys")
                foreach (var layer in new[] { "dependency", "project" })
                    Assert.Equal(build, text.Contains(layer + "_key=", StringComparison.Ordinal));
            else if (!build) Assert.Equal("", text);
        }
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));

        string Git(params string[] arguments)
        {
            var result = Run("git", arguments, fixture.Root);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }
    }
}
