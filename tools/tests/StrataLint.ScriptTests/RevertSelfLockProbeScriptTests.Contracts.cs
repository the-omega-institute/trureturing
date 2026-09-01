using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class RevertSelfLockProbeScriptTests
{
    [Fact]
    public void RealRunEdgeBinderBindsExactLastGreenToTargetFirstRed()
    {
        using var fixture = new RunEdgeFixture();

        var result = fixture.Bind(fixture.TargetMergeSha, duplicateRed: false);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        var edge = JsonNode.Parse(
            ScriptHarnessScratch.ReadScratchText(fixture.Output))!.AsObject();
        Assert.Equal(fixture.TargetMergeSha, edge["target_merge_sha"]!.GetValue<string>());
        Assert.Equal(fixture.LastGreenSha, edge["last_green_sha"]!.GetValue<string>());
        Assert.Equal(100, edge["last_green_run_id"]!.GetValue<long>());
        Assert.Equal(101, edge["first_red_run_id"]!.GetValue<long>());
    }

    [Fact]
    public void RealRunEdgeBinderRejectsDescendantRedRun()
    {
        using var fixture = new RunEdgeFixture();

        var result = fixture.Bind(fixture.DescendantSha, duplicateRed: false);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("SELF_LOCK_RED_EDGE_INVALID", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(ScriptHarnessScratch.ScratchFileExists(fixture.Output));
    }

    [Fact]
    public void RealRunEdgeBinderRejectsNonUniqueRedSelection()
    {
        using var fixture = new RunEdgeFixture();

        var result = fixture.Bind(fixture.TargetMergeSha, duplicateRed: true);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("SELF_LOCK_RED_EDGE_INVALID", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(ScriptHarnessScratch.ScratchFileExists(fixture.Output));
    }

    [Fact]
    public void RealTargetedRunnerRejectsJ0HeadChangedAfterSeal()
    {
        using var fixture = new TargetedCommandFixture();
        fixture.MoveHeadToBase();

        var result = fixture.RunTargeted();

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "SELF_LOCK_TARGET_EXECUTION_FAILED",
            Encoding.UTF8.GetString(result.StandardError));
    }

    private sealed class RunEdgeFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string controller;
        private readonly string greenRuns;
        private readonly string redRuns;
        private readonly string repository;
        private readonly string temporaryPath;

        internal RunEdgeFixture()
        {
            temporaryPath = temporary.Path;
            repository = Path.Combine(temporaryPath, "repository");
            greenRuns = Path.Combine(temporaryPath, "green.json");
            redRuns = Path.Combine(temporaryPath, "red.json");
            Output = Path.Combine(temporaryPath, "edge.json");
            controller = Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "tools", "StrataLint.EngineeringScope", "bin", "Release", "net10.0",
                "StrataLint.EngineeringScope.dll");
            ScriptHarnessScratch.EnsureDirectory(repository);
            Git("init", "--template=", "-b", "main");
            Git("config", "--local", "user.name", "Run Edge Test");
            Git("config", "--local", "user.email", "run-edge@example.invalid");
            Git("config", "--local", "commit.gpgsign", "false");
            Git("config", "--local", "tag.gpgsign", "false");
            Git("config", "--local", "core.hooksPath", "/dev/null");
            Commit("last green", "state.txt", "green\n");
            LastGreenSha = GitText("rev-parse", "HEAD");
            Git("checkout", "-b", "feature");
            Commit("feature", "state.txt", "red\n");
            var feature = GitText("rev-parse", "HEAD");
            Git("checkout", "main");
            TargetMergeSha = CommitTree(feature, [LastGreenSha, feature], "target merge");
            Git("reset", "--hard", TargetMergeSha);
            Commit("descendant", "descendant.txt", "later\n");
            DescendantSha = GitText("rev-parse", "HEAD");
        }

        internal string DescendantSha { get; }
        internal string LastGreenSha { get; }
        internal string Output { get; }
        internal string TargetMergeSha { get; }

        internal ProcessOutput Bind(string redHead, bool duplicateRed)
        {
            ScriptHarnessScratch.WriteScratchText(
                greenRuns,
                RunsJson([(100, LastGreenSha, "success")]));
            var red = new List<(long Id, string Sha, string Conclusion)>
            {
                (101, redHead, "failure"),
            };
            if (duplicateRed) red.Add((102, redHead, "failure"));
            ScriptHarnessScratch.WriteScratchText(redRuns, RunsJson(red));
            return RunController(
                "bind-red-edge",
                "--repository", repository,
                "--target-merge", TargetMergeSha,
                "--last-green-runs", greenRuns,
                "--first-red-runs", redRuns,
                "--output", Output);
        }

        private static string RunsJson(IReadOnlyList<(long Id, string Sha, string Conclusion)> runs)
        {
            var entries = string.Join(",", runs.Select(run =>
                $"{{\"id\":{run.Id},\"head_sha\":\"{run.Sha}\",\"event\":\"push\","
                + $"\"status\":\"completed\",\"conclusion\":\"{run.Conclusion}\"}}"));
            return $"{{\"total_count\":{runs.Count},\"workflow_runs\":[{entries}]}}\n";
        }

        private void Commit(string message, string path, string content)
        {
            ScriptHarnessScratch.WriteScratchText(Path.Combine(repository, path), content);
            Git("add", "--", path);
            Git("commit", "-m", message);
        }

        private string CommitTree(string treeSource, IReadOnlyList<string> parents, string message)
        {
            var arguments = new List<string>
            {
                "commit-tree", GitText("rev-parse", treeSource + "^{tree}"),
            };
            foreach (var parent in parents)
            {
                arguments.Add("-p");
                arguments.Add(parent);
            }
            arguments.Add("-m");
            arguments.Add(message);
            return GitText(arguments.ToArray());
        }

        private ProcessOutput RunController(params string[] arguments) => TestProcessRunner.Run(
            "/usr/bin/env",
            GitEnvironment(["dotnet", controller, "self-lock-probe", .. arguments]),
            temporaryPath,
            TestBudgets.ScriptProcessHangGuard,
            512 * 1024);

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                GitEnvironment(["/usr/bin/git", "-C", repository, .. arguments]),
                repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        private string GitText(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                GitEnvironment(["/usr/bin/git", "-C", repository, .. arguments]),
                repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private string[] GitEnvironment(IReadOnlyList<string> command) =>
        [
            "-u", "GIT_AUTHOR_NAME", "-u", "GIT_AUTHOR_EMAIL",
            "-u", "GIT_COMMITTER_NAME", "-u", "GIT_COMMITTER_EMAIL",
            "-u", "GIT_CONFIG", "-u", "GIT_CONFIG_PARAMETERS", "-u", "GIT_TEMPLATE_DIR",
            $"HOME={Path.Combine(temporaryPath, "home")}",
            "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_COUNT=0",
            .. command,
        ];

        public void Dispose() => temporary.Dispose();
    }
}
