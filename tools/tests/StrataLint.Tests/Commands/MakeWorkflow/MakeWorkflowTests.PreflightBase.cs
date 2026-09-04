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
        Assert.Contains("STRATALINT_SCRIBE_BASE=\"$BASE_SHA\"", script, StringComparison.Ordinal);
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

    [Fact]
    public void PreflightCallSitesMaterializeTheHeadParentSha()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var playbook = File.ReadAllText(Path.Combine(root, "tools/scripts/workflow/playbook-workflows.sh"));
        var land = File.ReadAllText(Path.Combine(root, "tools/scripts/agent/land.sh"));
        var formalize = File.ReadAllText(Path.Combine(root, "skills/codex-formalize/SKILL.md"));
        var ingest = File.ReadAllText(Path.Combine(root, "skills/codex-theory-ingest/SKILL.md"));
        const string invocation = "make preflight BASE=\"$(git rev-parse HEAD^1)\"";

        Assert.Contains("make preflight BASE=<40-hex-sha>", makefile, StringComparison.Ordinal);
        Assert.Contains(invocation, playbook, StringComparison.Ordinal);
        var landLines = land.Split('\n');
        var materialization = Array.FindIndex(
            landLines,
            static line => line.StartsWith("BASE=$(git rev-parse ", StringComparison.Ordinal));
        var preflight = Array.FindIndex(
            landLines,
            static line => line.Contains("make preflight", StringComparison.Ordinal));
        Assert.True(materialization >= 0 && materialization < preflight);
        Assert.Contains("BASE=\"$BASE\"", landLines[preflight], StringComparison.Ordinal);
        Assert.DoesNotContain("$(git rev-parse", landLines[preflight], StringComparison.Ordinal);
        Assert.DoesNotContain("BASE=$BASE", landLines[preflight], StringComparison.Ordinal);
        var formalizePreflightLines = formalize.Split('\n')
            .Where(static line => line.Contains("make preflight", StringComparison.Ordinal))
            .ToArray();
        var ingestPreflightLines = ingest.Split('\n')
            .Where(static line => line.Contains("make preflight", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(2, formalizePreflightLines.Length);
        Assert.Equal(2, ingestPreflightLines.Length);
        Assert.All(
            formalizePreflightLines,
            line => Assert.Contains(invocation, line, StringComparison.Ordinal));
        Assert.All(
            ingestPreflightLines,
            line => Assert.Contains(invocation, line, StringComparison.Ordinal));
        Assert.DoesNotContain(
            "make preflight BASE=$(git merge-base",
            formalize + ingest,
            StringComparison.Ordinal);
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
              "rev-parse HEAD") printf '%s\n' '{{GateCandidateSha}}' ;;
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
                $"PREFLIGHT_BASE_MODE=\"$1\" PREFLIGHT_BASE_INVOCATIONS=\"$2\" PATH=\"$3:/usr/bin:/bin\" {baseCommand} /bin/bash \"$4\"",
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
        var arguments = new List<string>();
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
