using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class PreflightLeanDonorTests
{
    [Theory]
    [InlineData("warm", 0, false)]
    [InlineData("warm", 23, false)]
    [InlineData("warm", 0, true)]
    [InlineData("missing", 0, false)]
    [InlineData("corrupt", 0, false)]
    [InlineData("partition", 0, false)]
    [InlineData("platform", 0, false)]
    [InlineData("busy", 0, false)]
    [InlineData("unavailable", 0, false)]
    [InlineData("not-git", 0, false)]
    [InlineData("native-environment-only", 0, false)]
    [InlineData("empty-wrapper", 0, false)]
    public void PrivatePrCandidateUsesReadOnlySourceDonorAndStillRunsProducer(string scenario, int producerExit, bool ensureFirst)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        using var directory = new TemporaryDirectory();
        var donor = Path.Combine(directory.Path, "donor");
        var source = Path.Combine(directory.Path, "source worktree");
        Directory.CreateDirectory(donor);
        var repository = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { "Makefile", "tools/scripts/preflight.sh", "tools/scripts/worktree/lean-cache-run.sh",
                     "tools/scripts/worktree/lean-cache-ensure.sh", "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
            Write(donor, path, File.ReadAllText(Path.Combine(repository, path)));
        Write(donor, ".gitignore", "build/\n.lake/\n");
        Write(donor, "lean-toolchain", "leanprover/lean4:v4.33.0\n");
        Write(donor, "lake-manifest.json", LeanCacheFixtureFile.Manifest());
        Write(donor, "Meta/FILEMAP.toml", """
            schema_version = 5
            resources = []
            evidence = { artifact_kinds = { json = { profile = "structured-json", selectors = ["result"], path_selectors = ["formal"] } } }
            [residence_policy]
            case_id = "FIXTURE"
            desired = "explicit"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "**"
            require = []
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["test"]
            verified_by = ["test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n");
        // Only the stage boundary and external Lake service are adapters. The
        // preflight, reader wrapper, native donor selection and copy are real.
        Write(donor, "tools/scripts/ci-stage.sh", """
            #!/bin/bash
            set -euo pipefail
            printf '%s\n' "$1" >> "$DONOR_TEST_STAGES"
            test -z "$(git remote)"
            test -z "$(git for-each-ref --format='%(refname)' refs/remotes/)"
            if [[ "$1" == current ]]; then
              if [[ -n "$DONOR_TEST_OVERRIDE" ]]; then export STRATALINT_LEAN_CACHE_DONOR_REPOSITORY="$DONOR_TEST_OVERRIDE"; fi
              if [[ "$DONOR_TEST_SCENARIO" == native-environment-only ]]; then
                exec dotnet "$STRATALINT_LEAN_PRODUCER_DLL" with-cache-reader -- "$DONOR_TEST_LAKE" build "$DONOR_TEST_EXIT"
              fi
              if [[ "$DONOR_TEST_SCENARIO" == empty-wrapper ]]; then STRATALINT_LEAN_CACHE_DONOR_REPOSITORY=; fi
              if [[ "$DONOR_TEST_ENSURE" == true ]]; then /bin/bash tools/scripts/worktree/lean-cache-ensure.sh; fi
              /bin/bash tools/scripts/worktree/lean-cache-run.sh "$DONOR_TEST_LAKE" build "$DONOR_TEST_EXIT"
            else
              test -z "${STRATALINT_LEAN_CACHE_DONOR_REPOSITORY:-}"
            fi
            """ + "\n");
        Write(donor, "tools/scripts/worktree/lean-cache-publish.sh",
            "#!/bin/sh\nprintf 'LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"fixture has no remote seed\"}\\n'\nexit 1\n");
        Git(donor, "init", "-q");
        Git(donor, "add", ".");
        Git(donor, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture");
        var basis = Git(donor, "rev-parse", "HEAD").Trim();
        Git(donor, "remote", "add", "origin", "https://example.invalid/unchanged.git");
        Git(donor, "update-ref", "refs/remotes/origin/dev", basis);
        Git(donor, "worktree", "add", "--detach", source, basis);
        Write(source, "head-input", "candidate input\n");
        Git(source, "add", "head-input");
        Git(source, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate");
        Assert.False(Directory.Exists(Path.Combine(source, ".lake")));
        if (scenario != "missing")
        {
            Write(donor, ".lake/build/lib/lean/Fixture.olean", "warm project material\n");
            Write(donor, ".lake/packages/mathlib/Mathlib/Fixture.lean", "def fixture := 0\n");
            Write(donor, ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean", "warm mathlib material\n");
            if (scenario == "partition") Write(donor, "lake-manifest.json", LeanCacheFixtureFile.Manifest('b'));
            LeanCacheStamp.Write(Path.Combine(donor, ".lake"), LeanPinSet.TryReadWorktree(donor, out _)!);
            if (scenario == "corrupt") Write(donor, ".lake/.stratalint-lean-cache-stamp.json", "broken stamp\n");
            if (scenario == "platform")
            {
                var stamp = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(LeanCacheStamp.PathFor(Path.Combine(donor, ".lake"))))!;
                stamp["arch"] = "foreign-architecture";
                Write(donor, ".lake/.stratalint-lean-cache-stamp.json", stamp.ToJsonString());
            }
        }
        var lake = Path.Combine(directory.Path, "lake");
        Write(directory.Path, "lake", """
            #!/bin/sh
            set -eu
            printf '%s\n' "$*" >> "$DONOR_TEST_CALLS"
            if [ "$1" = exe ]; then
              mkdir -p .lake/packages/mathlib/Mathlib .lake/packages/mathlib/.lake/build/lib/lean/Mathlib
              printf 'def fixture := 0\n' > .lake/packages/mathlib/Mathlib/Fixture.lean
              printf 'downloaded fixture\n' > .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean
              exit 0
            fi
            if [ -f .lake/build/lib/lean/Fixture.olean ]; then printf 'warm\n' >> "$DONOR_TEST_CALLS"; fi
            mkdir -p .lake/build
            printf 'private producer output\n' > .lake/build/producer-output
            printf 'producer executed\n'
            exit "$2"
            """ + "\n");
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var before = SourceState();
        var calls = Path.Combine(directory.Path, "calls");
        var stages = Path.Combine(directory.Path, "stages");
        using var busy = scenario == "busy" ? LeanCacheGuard.TryAcquireExclusive(Path.Combine(donor, ".lake")) : null;
        var result = TestProcessRunner.Run("/usr/bin/env", ["MODE=pr", "BASE=" + basis,
            "STRATALINT_LEAN_PRODUCER_DLL=" + typeof(LeanProgram).Assembly.Location,
            "STRATALINT_ACCEPT_COLD_BUILD=1", "STRATALINT_LEAN_CACHE_DONOR_REPOSITORY=", "CI_WORKFLOW_INPUTS=null",
            "GITHUB_EVENT_NAME=", "CANDIDATE_SHA=", "CI_BUILD_ROUND=", "CI_NEEDS={}",
            "DONOR_TEST_LAKE=" + lake, "DONOR_TEST_EXIT=" + producerExit.ToString(CultureInfo.InvariantCulture),
            "DONOR_TEST_SCENARIO=" + scenario,
            "LAKE_BIN=" + lake, "DONOR_TEST_ENSURE=" + ensureFirst.ToString().ToLowerInvariant(),
            "DONOR_TEST_OVERRIDE=" + (scenario == "unavailable" ? Path.Combine(directory.Path, "absent") : scenario == "not-git" ? directory.Path : ""),
            "DONOR_TEST_CALLS=" + calls, "DONOR_TEST_STAGES=" + stages,
            "make", "preflight", "MODE=pr", "BASE=" + basis], source,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == (producerExit == 0 ? 0 : 2), output);
        Assert.Contains("producer executed", output, StringComparison.Ordinal);
        Assert.Equal(producerExit == 0 ? ["engineering", "current", "delta"] : new[] { "engineering", "current" }, File.ReadAllLines(stages));
        Assert.Equal(before, SourceState());
        var candidate = output.Split('\n').Single(line => line.StartsWith("PREFLIGHT_CANDIDATE path=", StringComparison.Ordinal))["PREFLIGHT_CANDIDATE path=".Length..];
        Assert.False(Directory.Exists(candidate));
        var expected = scenario == "warm" ? new[] { "build " + producerExit, "warm" } : ["exe cache get", "build " + producerExit];
        Assert.True(expected.SequenceEqual(File.ReadAllLines(calls)),
            "PREFLIGHT_DONOR_NOT_USED: expected " + string.Join(",", expected) + "; actual " + File.ReadAllText(calls) + "\n" + output);
        if (scenario == "warm") Assert.Contains("\"status\":\"seeded\"", output, StringComparison.Ordinal);

        string SourceState() => JsonSerializer.Serialize(new[] { Git(donor, "rev-parse", "HEAD"), Git(source, "rev-parse", "HEAD"),
            Git(source, "status", "--porcelain", "--untracked-files=all"), Git(donor, "remote", "-v"),
            Git(donor, "for-each-ref", "--format=%(refname) %(objectname)", "refs/remotes/"),
            Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(Git(source, "rev-parse", "--git-path", "index").Trim()))),
            JsonSerializer.Serialize(Directory.Exists(Path.Combine(donor, ".lake"))
                ? Directory.GetFiles(Path.Combine(donor, ".lake"), "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal)
                    .Select(path => path + ":" + Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)))).ToArray() : []) });
    }

    [Theory]
    [InlineData("missing-value", false)]
    [InlineData("empty-value", false)]
    [InlineData("duplicate", false)]
    [InlineData("option-as-value", false)]
    [InlineData("missing-value", true)]
    [InlineData("empty-value", true)]
    [InlineData("duplicate", true)]
    [InlineData("option-as-value", true)]
    public void MalformedExplicitDonorIsAnInputError(string scenario, bool writer)
    {
        using var directory = new TemporaryDirectory();
        var options = scenario switch
        {
            "missing-value" => new[] { "--donor-repository" },
            "empty-value" => ["--donor-repository", ""],
            "option-as-value" => ["--donor-repository", "--path"],
            _ => ["--donor-repository", directory.Path, "--donor-repository", directory.Path],
        };
        var result = writer
            ? LeanCacheEnsureCommand.RunWithWriter(directory.Path, [.. options, "--", "unreachable-producer"],
                new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner())
            : LeanCacheEnsureCommand.Run(directory.Path, options,
                new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());
        Assert.False(result.Success);
        Assert.StartsWith("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(directory.Path, ".lake")));
    }

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == 0, text);
        return Encoding.UTF8.GetString(result.StandardOutput);
    }

    private static void Write(string root, string relative, string text)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, text);
    }
}
