using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private static void AssertNativeEngineeringDispatch(string sourceRoot)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(fixture.Path, "Meta"));
        Directory.CreateDirectory(Path.Combine(fixture.Path, "notes"));
        File.WriteAllText(Path.Combine(fixture.Path, "Meta/FILEMAP.toml"), """
            [[files]]
            pattern = "notes/**"
            admission_plane = "content"
            [[files]]
            pattern = "Meta/FILEMAP.toml"
            admission_plane = "judge"
            [[files]]
            pattern = "Meta/EngineeringInputs.json"
            admission_plane = "judge"
            kind = "program"
            artifact_id = "EngineeringInputManifest"
            consumed_by = ["EngineeringInputManifest"]
            verified_by = ["EngineeringInputManifest"]
            runtime_disposition = "committed-source"
            """);
        File.WriteAllText(Path.Combine(fixture.Path, "Meta/EngineeringInputs.json"), """
            {"schema_version":1,"projects":[],"inputs":[{"patterns":["Meta/**","notes/**"],"projects":[]}]}
            """);
        RunScenarioGit(fixture.Path, "init", "--quiet");
        RunScenarioGit(fixture.Path, "config", "user.name", "Engineering dispatch fixture");
        RunScenarioGit(fixture.Path, "config", "user.email", "dispatch@example.invalid");
        void Commit()
        {
            RunScenarioGit(fixture.Path, "add", ".");
            RunScenarioGit(fixture.Path, "commit", "--quiet", "-m", "fixture input");
        }
        string Git(params string[] arguments) => RunScenarioGitForOutput(fixture.Path, arguments).Trim();
        Commit();
        var before = Git("rev-parse", "HEAD");
        File.WriteAllText(Path.Combine(fixture.Path, "notes/earlier.md"), "earlier input\n");
        Commit();
        File.WriteAllText(Path.Combine(fixture.Path, "notes/latest.md"), "latest input\n");
        Commit();
        var head = Git("rev-parse", "HEAD");

        using var commandFixture = new TemporaryDirectory();
        var dotnet = TestProcessRunner.Run("/bin/bash", ["-c", "command -v dotnet"],
            sourceRoot, TestBudgets.ScriptProcessHangGuard, 4096);
        Assert.Equal(0, dotnet.ExitCode);
        var realDotnet = Encoding.UTF8.GetString(dotnet.StandardOutput).Trim();
        WriteExecutable(Path.Combine(commandFixture.Path, "dotnet"), """
            #!/bin/bash
            if [[ "${MSBUILDDISABLENODEREUSE:-}" != 1 ]]; then
              printf 'engineering dotnet requires delegated MSBUILDDISABLENODEREUSE=1; actual=%s\n' "${MSBUILDDISABLENODEREUSE:-}" >&2
              exit 97
            fi
            [[ "${1:-}" == run ]] || exit 64
            shift
            exec "$ENGINEERING_REAL_DOTNET" run --no-build "$@"
            """);

        ProcessOutput Plan(string eventKind, string endpoint, string candidate) => TestProcessRunner.Run(
            "env",
            ["MSBUILDDISABLENODEREUSE=0", "ENGINEERING_REAL_DOTNET=" + realDotnet,
                "PATH=" + commandFixture.Path + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
                "make", "--no-print-directory", "-C", Path.Combine(sourceRoot, "tools"), "engineering-tests",
                "REPOSITORY=" + fixture.Path, "EVENT=" + eventKind, "HEAD=" + candidate,
                (eventKind == "push" ? "BEFORE=" : "BASE=") + endpoint, "PLAN_ONLY=1"],
            sourceRoot, TestBudgets.ScriptProcessHangGuard, 128 * 1024);

        var push = Plan("push", before, head);
        Assert.True(push.ExitCode == 0, Encoding.UTF8.GetString(push.StandardError));
        var output = Encoding.UTF8.GetString(push.StandardOutput);
        Assert.Contains($"event=push mode=endpoints before={before} head={head}", output, StringComparison.Ordinal);
        Assert.Contains("notes/earlier.md", output, StringComparison.Ordinal);
        Assert.Contains("notes/latest.md", output, StringComparison.Ordinal);
        Assert.Contains("not-required", output, StringComparison.Ordinal);

        var merge = Git("commit-tree", Git("rev-parse", "HEAD^{tree}"), "-p", before, "-p", head, "-m", "checked merge");
        RunScenarioGit(fixture.Path, "checkout", "--detach", merge);
        var pr = Plan("pull-request", before, merge);
        Assert.True(pr.ExitCode == 0, Encoding.UTF8.GetString(pr.StandardError));
        Assert.Contains($"event=pull-request mode=endpoints before={before} head={merge}",
            Encoding.UTF8.GetString(pr.StandardOutput), StringComparison.Ordinal);
        var invalid = Plan("pull-request", head, merge);
        Assert.Equal(2, invalid.ExitCode);
        Assert.Contains("PR --base must equal checked merge first parent",
            Encoding.UTF8.GetString(invalid.StandardError), StringComparison.Ordinal);
    }
}
