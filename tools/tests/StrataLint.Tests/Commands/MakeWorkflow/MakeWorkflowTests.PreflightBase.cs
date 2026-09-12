using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void PreflightRejectsMissingBaseBeforeToolLookup()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("missing", null);

        AssertPreflightBaseInvalid(result, "missing", expectGit: false);
    }

    [Fact]
    public void PreflightRejectsNonCanonicalBaseBeforeToolLookup()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation(
            "not-40-hex",
            "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");

        AssertPreflightBaseInvalid(result, "not-40-hex", expectGit: false);
    }

    [Fact]
    public void PreflightRejectsMissingObject()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("object-missing", GateForkSha);

        AssertPreflightBaseInvalid(result, "object-missing", expectGit: true);
    }

    [Fact]
    public void PreflightRejectsNonCommitObject()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("not-commit", GateForkSha);

        AssertPreflightBaseInvalid(result, "not-commit", expectGit: true);
    }

    [Fact]
    public void PreflightRejectsNonAncestorCommit()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("not-ancestor", GateForkSha);

        AssertPreflightBaseInvalid(result, "not-ancestor", expectGit: true);
    }

    [Fact]
    public void PreflightReportsAncestorCheckFailureDistinctly()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("ancestor-check-failed", GateForkSha);

        AssertPreflightBaseInvalid(result, "ancestor-check-failed", expectGit: true);
    }

    [Fact]
    public void PreflightUsesOnlyExplicitBaseAndCanonicalCandidateReferences()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        Assert.Contains("BASE_SHA=\"$BASE\"", script, StringComparison.Ordinal);
        Assert.Contains("git cat-file -t \"$BASE\"", script, StringComparison.Ordinal);
        Assert.Contains("git merge-base --is-ancestor \"$BASE\" HEAD", script, StringComparison.Ordinal);
        Assert.Contains("CANDIDATE_SHA=\"$(git rev-parse HEAD)\"", script, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_PUSH_BEFORE=\"$ENGINEERING_BEFORE\"", script, StringComparison.Ordinal);
        Assert.Contains("make gate BASE=\"$BASE_SHA\" GATE_ARGS=\"--skip-engineering\"", script, StringComparison.Ordinal);
        Assert.DoesNotContain("BASE_REF", script, StringComparison.Ordinal);
        Assert.DoesNotContain("BASE_TIP_SHA", script, StringComparison.Ordinal);
        Assert.DoesNotContain("admission-base-lib.sh", script, StringComparison.Ordinal);
        Assert.DoesNotContain("admission_resolve_base", script, StringComparison.Ordinal);
        Assert.DoesNotContain("git fetch", script, StringComparison.Ordinal);
        Assert.DoesNotContain("git remote", script, StringComparison.Ordinal);
        Assert.DoesNotContain("BASE_ADVANCED", script, StringComparison.Ordinal);
        Assert.DoesNotContain("origin/", script, StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightAcceptsAnExplicitAncestorBeforeStartingExpensiveStages()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightBaseValidation("accepted", GateForkSha);
        var error = Encoding.UTF8.GetString(result.Process.StandardError);

        Assert.True(
            result.Process.ExitCode == 86,
            $"expected exit 86, actual {result.Process.ExitCode}; invocations: "
            + string.Join(" | ", result.Invocations)
            + "; stdout: " + Encoding.UTF8.GetString(result.Process.StandardOutput)
            + "; stderr: " + error);
        Assert.DoesNotContain("PREFLIGHT_BASE_INVALID", error, StringComparison.Ordinal);
        Assert.Equal(
            [
                "dotnet:--version",
                "lake:--version",
                "git:rev-parse --show-toplevel",
                $"git:cat-file -t {GateForkSha}",
                $"git:merge-base --is-ancestor {GateForkSha} HEAD",
                "git:rev-parse HEAD",
                "git:rev-parse --verify HEAD",
                "dotnet:restore tools/tests/CompileFailProof/CompileFailProof.csproj --locked-mode",
            ],
            result.Invocations);
    }

    [Fact]
    public void PreflightMakeTargetClearsOnlyTheFileDefault()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var scriptDirectory = Path.Combine(fixture.Path, "tools", "scripts");
        Directory.CreateDirectory(scriptDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        WriteExecutable(
            Path.Combine(scriptDirectory, "preflight.sh"),
            "#!/usr/bin/env bash\nprintf '<%s>\\n' \"${BASE-__unset__}\"");

        var inherited = RunMakePreflight(fixture.Path, null, null);
        var environment = RunMakePreflight(fixture.Path, GateForkSha, null);
        var commandLine = RunMakePreflight(fixture.Path, null, GateCandidateSha);

        Assert.Equal("<>\n", Encoding.UTF8.GetString(inherited.StandardOutput));
        Assert.Equal($"<{GateForkSha}>\n", Encoding.UTF8.GetString(environment.StandardOutput));
        Assert.Equal($"<{GateCandidateSha}>\n", Encoding.UTF8.GetString(commandLine.StandardOutput));
    }

    [Theory]
    [InlineData("deliver", "missing")]
    [InlineData("deliver", "invalid")]
    [InlineData("deliver", "unavailable")]
    [InlineData("land", "missing")]
    [InlineData("land", "invalid")]
    [InlineData("land", "unavailable")]
    public void DeliveryCallersRejectMissingRangeBeforeDerivation(string caller, string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        var (process, calls) = RunDeliveryCaller(caller, mode);
        Assert.Equal(2, process.ExitCode);
        Assert.Contains("PREFLIGHT_PUSH_RANGE_INVALID", Encoding.UTF8.GetString(process.StandardError));
        Assert.DoesNotContain(calls, call => call.StartsWith("make:", StringComparison.Ordinal)
            || call.StartsWith("dotnet:", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("deliver", 2)]
    [InlineData("land", 94)]
    public void DeliveryCallersPropagateBeforeAndPreserveConfigurationFailure(string caller, int expected)
    {
        if (OperatingSystem.IsWindows()) return;
        var (process, calls) = RunDeliveryCaller(caller, "valid");
        Assert.True(process.ExitCode == expected, Encoding.UTF8.GetString(process.StandardOutput)
            + Encoding.UTF8.GetString(process.StandardError));
        Assert.Contains(calls, call => call.StartsWith("make:preflight BASE=", StringComparison.Ordinal)
            && call.Contains(" BEFORE=", StringComparison.Ordinal));
        Assert.DoesNotContain(calls, call => call.StartsWith("git:add", StringComparison.Ordinal)
            || call.StartsWith("git:push", StringComparison.Ordinal) || call.StartsWith("git:commit", StringComparison.Ordinal));
    }

    [Fact]
    public void DeliveryExplicitPreflightSkipReportsNotRun()
    {
        if (OperatingSystem.IsWindows()) return;
        var (process, calls) = RunDeliveryCaller("deliver", "skip");
        Assert.True(process.ExitCode == 0, Encoding.UTF8.GetString(process.StandardError));
        Assert.Contains("LOCAL_PREFLIGHT_NOT_RUN explicit_skip=1", Encoding.UTF8.GetString(process.StandardOutput));
        Assert.DoesNotContain(calls, call => call.StartsWith("make:preflight", StringComparison.Ordinal));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static (ProcessOutput Process, string[] Calls) RunDeliveryCaller(string caller, string mode)
    {
        using var fixture = new TemporaryDirectory();
        var root = fixture.Path;
        var source = TestRepositoryLayout.FindRoot();
        foreach (var relative in new[] { "Makefile", "tools/scripts/preflight.sh",
            "tools/scripts/workflow/playbook-workflows.sh", "tools/scripts/agent/land.sh" })
        {
            var target = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(source, relative), target);
        }
        RunScenarioGit(root, "init", "--quiet");
        RunScenarioGit(root, "add", ".");
        RunScenarioGit(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "--no-gpg-sign", "-m", "fixture");
        var before = RunScenarioGitForOutput(root, "rev-parse", "HEAD").Trim();
        var bin = Path.Combine(root, "bin");
        Directory.CreateDirectory(bin);
        var log = Path.Combine(root, "calls");
        File.WriteAllText(Path.Combine(root, "message.msg"), "fixture\n");
        Directory.CreateDirectory(Path.Combine(root, "Generated"));
        File.WriteAllText(Path.Combine(root, "Generated/truth-graph.v1.json"), "{\"truth\":{\"nodes\":[]}}");
        WriteExecutable(Path.Combine(bin, "make"), """
            #!/usr/bin/env bash
            printf 'make:%s\n' "$*" >> "$DELIVERY_CALLS"
            if [[ "$1" == preflight ]]; then
              [[ "$*" == "preflight BASE=$DELIVERY_BEFORE BEFORE=$DELIVERY_BEFORE" ]] || exit 71
              echo 'PREFLIGHT_PUSH_RANGE_INVALID reason=configuration-fixture' >&2
              exit 2
            fi
            """);
        WriteExecutable(Path.Combine(bin, "dotnet"), """
            #!/usr/bin/env bash
            printf 'dotnet:%s\n' "$*" >> "$DELIVERY_CALLS"
            """);
        WriteExecutable(Path.Combine(bin, "git"), """
            #!/usr/bin/env bash
            printf 'git:%s\n' "$*" >> "$DELIVERY_CALLS"
            case "$1" in
              fetch|checkout|merge) exit 0 ;;
              add|commit|push) exit 89 ;;
            esac
            if [[ "$*" == 'rev-parse origin/dev' ]]; then printf '%s\n' "$DELIVERY_BEFORE"; exit 0; fi
            exec /usr/bin/git "$@"
            """);
        var value = mode == "invalid" ? "HEAD^1" : mode == "unavailable" ? new string('a', 40)
            : mode is "missing" or "skip" ? "" : before;
        string[] command = caller == "deliver" ? ["/usr/bin/make", "--no-print-directory", "deliver-check", $"BASE={before}"]
            : ["/bin/bash", Path.Combine(root, "tools/scripts/agent/land.sh"), root, "fixture", Path.Combine(root, "message.msg")];
        var result = TestProcessRunner.Run("env", ["-u", "MAKEFLAGS", "-u", "MAKELEVEL",
            $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}", $"BEFORE={value}",
            $"PREFLIGHT={(mode == "skip" ? 0 : 1)}", $"LAND_LOG_DIR={Path.Combine(root, "logs")}",
            $"DELIVERY_CALLS={log}", $"DELIVERY_BEFORE={before}", .. command], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        return (result, File.Exists(log) ? File.ReadAllLines(log) : []);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static PreflightBaseResult RunPreflightBaseValidation(string mode, string? @base)
    {
        using var fixture = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var bin = Path.Combine(fixture.Path, "bin");
        var invocations = Path.Combine(fixture.Path, "invocations");
        Directory.CreateDirectory(bin);
        WriteExecutable(
            Path.Combine(bin, "git"),
            $$"""
            #!/usr/bin/env bash
            printf 'git:%s\n' "$*" >> "$PREFLIGHT_BASE_INVOCATIONS"
            case "$*" in
              "rev-parse --show-toplevel") printf '%s\n' '{{root}}' ;;
              "cat-file -t {{GateForkSha}}")
                [[ "$PREFLIGHT_BASE_MODE" != object-missing ]] || exit 1
                [[ "$PREFLIGHT_BASE_MODE" != not-commit ]] || { printf 'blob\n'; exit 0; }
                printf 'commit\n'
                ;;
              "merge-base --is-ancestor {{GateForkSha}} HEAD")
                [[ "$PREFLIGHT_BASE_MODE" != not-ancestor ]] || exit 1
                [[ "$PREFLIGHT_BASE_MODE" != ancestor-check-failed ]] || exit 91
                exit 0
                ;;
              "rev-parse HEAD"|"rev-parse --verify HEAD") printf '%s\n' '{{GateCandidateSha}}' ;;
              *) exit 97 ;;
            esac
            """);
        WriteExecutable(
            Path.Combine(bin, "dotnet"),
            "#!/usr/bin/env bash\nprintf 'dotnet:%s\\n' \"$*\" >> \"$PREFLIGHT_BASE_INVOCATIONS\"\n"
            + "[[ \"${1:-}\" == --version ]] && exit 0\n[[ \"${1:-}\" == restore ]] && exit 86\nexit 87");
        WriteExecutable(
            Path.Combine(bin, "lake"),
            "#!/usr/bin/env bash\nprintf 'lake:%s\\n' \"$*\" >> \"$PREFLIGHT_BASE_INVOCATIONS\"\nexit 0");
        WriteExecutable(
            Path.Combine(bin, "make"),
            "#!/usr/bin/env bash\nprintf 'make:%s\\n' \"$*\" >> \"$PREFLIGHT_BASE_INVOCATIONS\"\nexit 88");

        var baseCommand = @base is null ? "env -u BASE" : "BASE=\"$5\"";
        var process = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                $"BEFORE=0000000000000000000000000000000000000000 PREFLIGHT_BASE_MODE=\"$1\" PREFLIGHT_BASE_INVOCATIONS=\"$2\" PATH=\"$3:/usr/bin:/bin\" {baseCommand} /bin/bash \"$4\"",
                "preflight-base",
                mode,
                invocations,
                bin,
                Path.Combine(root, PreflightScriptPath),
                @base ?? string.Empty,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        return new PreflightBaseResult(
            process,
            File.Exists(invocations) ? File.ReadAllLines(invocations) : []);
    }

    private static void AssertPreflightBaseInvalid(
        PreflightBaseResult result,
        string reason,
        bool expectGit)
    {
        Assert.Equal(2, result.Process.ExitCode);
        Assert.Empty(result.Process.StandardOutput);
        Assert.Equal(
            $"PREFLIGHT_BASE_INVALID reason={reason}\n",
            Encoding.UTF8.GetString(result.Process.StandardError));
        Assert.Equal(expectGit, result.Invocations.Any(static line => line.StartsWith(
            "git:",
            StringComparison.Ordinal)));
    }

    private static ProcessOutput RunMakePreflight(
        string root,
        string? environmentBase,
        string? commandLineBase)
    {
        // MAKEFLAGS carries an ancestor make's command-line variables and a nested make
        // re-reads them as command-line origin, so clearing only BASE would let an outer
        // `make ... BASE=<sha>` decide this test's verdict. CI proved it: the engineering
        // job runs `make ... BASE=$ENGINEERING_BASE`, and this case observed that SHA
        // instead of the cleared file default. Judge the Makefile, not the ancestor.
        var arguments = new List<string> { "-u", "MAKEFLAGS", "-u", "MAKELEVEL" };
        if (environmentBase is null) arguments.AddRange(["-u", "BASE"]);
        else arguments.Add($"BASE={environmentBase}");
        arguments.Add("make");
        arguments.Add("--no-print-directory");
        arguments.Add("preflight");
        if (commandLineBase is not null) arguments.Add($"BASE={commandLineBase}");
        return TestProcessRunner.Run(
            "/usr/bin/env",
            arguments,
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
    }

    private sealed record PreflightBaseResult(
        ProcessOutput Process,
        IReadOnlyList<string> Invocations);
}
