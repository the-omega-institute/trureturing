using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class PreflightProcessContractTests
{
    [Fact]
    public void FailedCurrentDiagnosticsSurvivePrCandidateCleanupWithoutSuccessfulEvidence()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        fixture.Write(".gitignore", "build/\n");
        fixture.Write("tools/scripts/ci-stage.sh", """
            #!/bin/bash
            printf '%s\n' "$1" >> "$CONTRACT_CALLS"
            mkdir -p build/ci
            printf 'build/ci/engineering-paths.nul\0' > build/ci/engineering-paths.nul
            if [[ "$1" == current ]]; then
              mkdir -p build/ci/logs/current/lean-inspector
              printf 'raw cold build output\n' > build/ci/logs/current/lean-inspector/build.stdout.log
              printf '{"stage":"current","exit":2}\n' > build/ci/current-result.json
              exit 124
            fi
            """);
        fixture.Commit();
        var source = fixture.SourceState();
        var result = fixture.Preflight("pr", fixture.Git("rev-parse", "HEAD").Trim());
        Assert.Equal(2, result.Exit);
        Assert.Equal(new[] { "engineering", "current" }, fixture.Calls());
        Assert.Contains("PREFLIGHT_RESULT mode=pr stage=current exit=2 raw_exit=124", result.Text, StringComparison.Ordinal);
        Assert.Equal(source, fixture.SourceState());
        var lines = result.Text.Split('\n');
        var candidate = lines.Single(line => line.StartsWith("PREFLIGHT_CANDIDATE path=", StringComparison.Ordinal))["PREFLIGHT_CANDIDATE path=".Length..];
        Assert.False(TemporaryFileSystem.Directory.Exists(candidate));
        var archive = lines.Single(line => line.StartsWith("PREFLIGHT_ARTIFACT bundle=", StringComparison.Ordinal))["PREFLIGHT_ARTIFACT bundle=".Length..];
        using var gzip = new System.IO.Compression.GZipStream(File.OpenRead(archive), System.IO.Compression.CompressionMode.Decompress);
        using var tar = new System.Formats.Tar.TarReader(gzip);
        var entries = new Dictionary<string, string>();
        while (tar.GetNextEntry() is { } entry)
            if (entry.DataStream is { } data)
                entries.Add(entry.Name, new StreamReader(data).ReadToEnd());
        Assert.Equal("raw cold build output\n", entries["build/ci/logs/current/lean-inspector/build.stdout.log"]);
        Assert.Equal("{\"stage\":\"current\",\"exit\":2}\n", entries["build/ci/current-result.json"]);
        Assert.DoesNotContain("build/ci/current.json", entries.Keys);
        Assert.DoesNotContain(CommonExecutionEvidence.ReportPath, entries.Keys);
    }

    [Theory]
    [InlineData("")]
    [InlineData("push")]
    public void DefaultPushRunsCommonStagesOnceWithoutParentOrRemote(string mode)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var source = fixture.SourceState();
        var result = fixture.Preflight(mode, "");
        Assert.Equal(0, result.Exit);
        Assert.Equal(new[] { "engineering", "current" }, fixture.Calls());
        Assert.All(fixture.Observations(), observation =>
        {
            Assert.Equal(source.Head, observation.Commit);
            Assert.Equal(source.Tree, observation.Tree);
            Assert.Equal(source.Tree, observation.IndexTree);
            Assert.Empty(observation.Parents);
            Assert.Empty(observation.Status);
            Assert.Empty(observation.Remotes);
            Assert.Empty(observation.RemoteRefs);
            Assert.Single(observation.Arguments);
        });
        Assert.Equal(source, fixture.SourceState());
    }

    [Theory]
    [InlineData("unstaged")]
    [InlineData("staged")]
    [InlineData("untracked")]
    public void DirtyPushRunsCurrentWorktreeWithoutRequiringBase(string dirty)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        fixture.MakeDirty(dirty);
        var source = fixture.SourceState();
        Assert.NotEmpty(source.Status);
        var result = fixture.Preflight("push", "not-an-immutable-base");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "engineering", "current" }, fixture.Calls());
        Assert.All(fixture.Observations(), observation =>
        {
            Assert.Equal(source.Head, observation.Commit);
            Assert.Equal(source.Tree, observation.Tree);
            Assert.Equal(source.Status, observation.Status);
            Assert.Single(observation.Arguments);
        });
        Assert.Equal(source, fixture.SourceState());
        Assert.Equal("dirty", File.ReadAllText(Path.Combine(fixture.Root, dirty == "untracked" ? "untracked" : "tracked")));
    }

    [Fact]
    public void DivergentPrChecksSynthesizedTreeAndCleansCandidate()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var (basis, head, tree) = fixture.Diverge();
        var source = fixture.SourceState();
        var result = fixture.Preflight("pr", basis);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "engineering", "current", "delta" }, fixture.Calls());
        Assert.Contains("merged=yes", result.Text, StringComparison.Ordinal);
        AssertCandidate(fixture, basis, head, tree, [basis, head]);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, "base-only")));
        Assert.Equal("candidate data", File.ReadAllText(Path.Combine(fixture.Root, "head-only")));
        Assert.Equal(source, fixture.SourceState());
        var candidateLine = result.Text.Split('\n').Single(line => line.StartsWith("PREFLIGHT_CANDIDATE path=", StringComparison.Ordinal));
        Assert.False(TemporaryFileSystem.Directory.Exists(candidateLine["PREFLIGHT_CANDIDATE path=".Length..]));
    }

    [Fact]
    public void EqualBaseAndHeadCreatesCleanCandidateWithOneUniqueParent()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var source = fixture.SourceState();
        var tree = fixture.Git("merge-tree", "--write-tree", source.Head, source.Head).Trim();
        var result = fixture.Preflight("pr", source.Head);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "engineering", "current", "delta" }, fixture.Calls());
        AssertCandidate(fixture, source.Head, source.Head, tree, [source.Head]);
        Assert.Equal(source, fixture.SourceState());
    }

    private static void AssertCandidate(Fixture fixture, string basis, string head, string tree, string[] parents)
    {
        var observations = fixture.Observations();
        Assert.All(observations, observation =>
        {
            Assert.Equal(tree, observation.Tree);
            Assert.Equal(tree, observation.IndexTree);
            Assert.NotEqual(head, observation.Commit);
            Assert.NotEqual(basis, observation.Commit);
            Assert.Equal(parents, observation.Parents);
            Assert.Empty(observation.Status);
            Assert.Empty(observation.Remotes);
            Assert.Empty(observation.RemoteRefs);
            Assert.Equal(observation.Arguments[0] == "delta" ? new[] { "delta", basis } : [observation.Arguments[0]],
                observation.Arguments);
        });
        Assert.Single(observations.Select(observation => observation.Commit).Distinct(StringComparer.Ordinal));
        foreach (var observation in observations)
        {
            var plan = fixture.Selection(observation.Arguments[0]);
            Assert.Equal(observation.Commit, plan.GetProperty("candidate").GetProperty("commit").GetString());
            Assert.Equal(tree, plan.GetProperty("candidate").GetProperty("tree").GetString());
            Assert.Equal(basis, plan.GetProperty("base").GetString());
            Assert.Equal(head, plan.GetProperty("head").GetString());
            Assert.Equal("pr", plan.GetProperty("mode").GetString());
        }
    }

    [Theory]
    [InlineData("", "")]
    [InlineData("dev", "")]
    [InlineData("0000000000000000000000000000000000000000", "")]
    [InlineData("TREE", "")]
    [InlineData("BLOB", "")]
    [InlineData("HEAD", "untracked")]
    [InlineData("HEAD", "unstaged")]
    [InlineData("HEAD", "staged")]
    public void InvalidBaseOrUntrackedInputRejectsBeforeStages(string basis, string dirty)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        if (basis == "HEAD") basis = fixture.Git("rev-parse", "HEAD").Trim();
        if (basis == "TREE") basis = fixture.Git("rev-parse", "HEAD^{tree}").Trim();
        if (basis == "BLOB") basis = fixture.Git("rev-parse", "HEAD:tracked").Trim();
        if (dirty.Length != 0) fixture.MakeDirty(dirty);
        var source = fixture.SourceState();
        Assert.Equal(2, fixture.Preflight("pr", basis).Exit);
        Assert.Empty(fixture.Calls());
        Assert.Equal(source, fixture.SourceState());
    }

    [Theory]
    [InlineData(1)]
    [InlineData(128)]
    public void FailedCleanlinessObservationRejectsBeforeMergeAndStages(int statusExit)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var basis = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.FailStatus(statusExit);
        var result = fixture.Preflight("pr", basis);
        Assert.True(result.Exit == 2,
            $"{result.Text}\nGit calls: {string.Join(",", fixture.GitCalls())}; stages: {string.Join(",", fixture.Calls())}");
        Assert.Contains("status observation failed", result.Error, StringComparison.Ordinal);
        Assert.Contains("PREFLIGHT_RESULT mode=pr stage=input exit=2 raw_exit=2 reason=status-observation-failed",
            result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "status" }, fixture.GitCalls());
        Assert.Empty(fixture.Calls());
    }

    [Fact]
    public void ConflictStopsBeforeExecutingCandidate()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        fixture.Write("conflict", "original"); fixture.Commit();
        var fork = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Write("conflict", "base"); fixture.Commit();
        var basis = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Git("checkout", "--detach", fork);
        fixture.Write("conflict", "head"); fixture.Commit();
        var result = fixture.Preflight("pr", basis);
        Assert.Equal(1, result.Exit);
        Assert.Empty(fixture.Calls());
    }

    [Theory]
    [InlineData("1", 1)]
    [InlineData("19", 2)]
    [InlineData("3", 2)]
    public void CommonFailureStopsLaterStagesAndNormalizesExit(string raw, int expected)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        Assert.Equal(expected, fixture.Preflight("push", "", raw).Exit);
        Assert.Equal(new[] { "engineering" }, fixture.Calls());
    }

    private sealed class Fixture : IDisposable
    {
        private readonly string scratch = TemporaryFileSystem.Directory.CreateTempSubdirectory("preflight-contract-").FullName;
        internal string Root => Path.Combine(scratch, "repository");
        private string CallsPath => Path.Combine(scratch, "calls");
        private string GitCallsPath => Path.Combine(scratch, "git-calls");
        private string ObservationsPath => Path.Combine(scratch, "observations");
        private string? gitBin;
        private string? realGit;
        internal Fixture(string preflightScript)
        {
            TemporaryFileSystem.Directory.CreateDirectory(Root);
            Write("tools/scripts/preflight.sh", preflightScript);
            foreach (var path in new[] { "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py" })
                Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
            Write(".gitignore", "build/\n");
            Write("Meta/FILEMAP.toml", """
                schema_version = 3
                resources = []
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
            Write("tracked", "original");
            WriteStageProbe();
            Git("init", "-q"); Git("config", "user.name", "Fixture"); Git("config", "user.email", "fixture@example.invalid");
            Commit();
        }
        private void WriteStageProbe()
        {
            Write("tools/scripts/ci-stage.sh", """
                #!/bin/bash
                set -euo pipefail
                printf '%s\n' "$1" >> "$CONTRACT_CALLS"
                observation="$CONTRACT_OBSERVATIONS/$1"
                mkdir -p "$observation"
                git rev-parse HEAD > "$observation/commit"
                git rev-parse 'HEAD^{tree}' > "$observation/tree"
                git show -s --format=%P HEAD > "$observation/parents"
                # write-tree updates index caches; observe a copy to preserve dirty push input.
                cp "$(git rev-parse --git-path index)" "$observation/index"
                GIT_INDEX_FILE="$observation/index" git write-tree > "$observation/index-tree"
                git status --porcelain --untracked-files=all > "$observation/status"
                git remote > "$observation/remotes"
                git for-each-ref '--format=%(refname)' refs/remotes/ > "$observation/remote-refs"
                printf '%s\n' "$@" > "$observation/arguments"
                if [[ "${CI_PLAN_PATH:-}" != '' ]]; then cp "$CI_PLAN_PATH" "$observation/plan.json"; fi
                if [[ -f base-only && -f head-only ]]; then printf 'merged=yes\n'; fi
                exit "${CONTRACT_EXIT:-0}"
                """);
        }
        internal (string Basis, string Head, string Tree) Diverge()
        {
            // B's stage must never run; only H replaces it with the probe.
            Write("tools/scripts/ci-stage.sh", "#!/bin/bash\nexit 97\n");
            Commit();
            var fork = Git("rev-parse", "HEAD").Trim();
            Write("base-only", "base data"); Commit();
            var basis = Git("rev-parse", "HEAD").Trim();
            Git("checkout", "--detach", fork);
            WriteStageProbe();
            Write("head-only", "candidate data"); Commit();
            var head = Git("rev-parse", "HEAD").Trim();
            Assert.Equal(fork, Git("show", "-s", "--format=%P", basis).Trim());
            Assert.Equal(fork, Git("show", "-s", "--format=%P", head).Trim());
            var tree = Git("merge-tree", "--write-tree", basis, head).Trim();
            Assert.NotEqual(Git("rev-parse", basis + "^{tree}").Trim(), tree);
            Assert.NotEqual(Git("rev-parse", head + "^{tree}").Trim(), tree);
            return (basis, head, tree);
        }
        internal void MakeDirty(string kind)
        {
            Write(kind == "untracked" ? "untracked" : "tracked", "dirty");
            if (kind == "staged") Git("add", "tracked");
        }
        internal (string Head, string Tree, string Index, string Status) SourceState()
        {
            var status = Git("status", "--porcelain", "--untracked-files=all");
            return (Git("rev-parse", "HEAD").Trim(), Git("rev-parse", "HEAD^{tree}").Trim(),
                Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(Path.Combine(Root, ".git/index")))), status);
        }
        internal Observation[] Observations() => Calls().Select(stage =>
        {
            string Read(string name) => File.ReadAllText(Path.Combine(ObservationsPath, stage, name));
            string[] Lines(string name) => Read(name).Split('\n', StringSplitOptions.RemoveEmptyEntries);
            return new Observation(Read("commit").Trim(), Read("tree").Trim(),
                Read("parents").Split([' ', '\n'], StringSplitOptions.RemoveEmptyEntries),
                Read("index-tree").Trim(), Read("status"), Lines("remotes"), Lines("remote-refs"), Lines("arguments"));
        }).ToArray();
        internal sealed record Observation(string Commit, string Tree, string[] Parents, string IndexTree,
            string Status, string[] Remotes, string[] RemoteRefs, string[] Arguments);
        internal System.Text.Json.JsonElement Selection(string stage) => System.Text.Json.JsonDocument.Parse(
            File.ReadAllText(Path.Combine(ObservationsPath, stage, "plan.json"))).RootElement.Clone();
        internal void Write(string path, string text)
        {
            var full = Path.Combine(Root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, text);
        }
        internal void Commit() { Git("add", "."); Git("commit", "-qm", "fixture"); }
        internal void FailStatus(int exit)
        {
            realGit = Run("/bin/bash", ["-c", "command -v git"]).Text.Trim();
            gitBin = Path.Combine(scratch, "bin");
            TemporaryFileSystem.Directory.CreateDirectory(gitBin);
            var shim = Path.Combine(gitBin, "git");
            TemporaryFileSystem.File.WriteAllText(shim, $$"""
                #!/bin/bash
                case "$1" in
                  status)
                    printf 'status\n' >> "$CONTRACT_GIT_CALLS"
                    printf 'status observation failed\n' >&2
                    exit {{exit}}
                    ;;
                  merge-tree) printf 'merge-tree\n' >> "$CONTRACT_GIT_CALLS" ;;
                esac
                exec "$CONTRACT_REAL_GIT" "$@"
                """);
            if (!OperatingSystem.IsWindows())
                File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
        internal string Git(params string[] args)
        {
            var result = Run("git", args);
            Assert.True(result.Exit == 0, result.Text);
            return result.Text;
        }
        internal (int Exit, string Text, string Error) Preflight(string mode, string basis, string raw = "0")
        {
            var environment = new Dictionary<string, string> { ["MODE"] = mode, ["BASE"] = basis, ["CONTRACT_CALLS"] = CallsPath,
                ["CONTRACT_OBSERVATIONS"] = ObservationsPath, ["CONTRACT_EXIT"] = raw };
            if (gitBin is not null)
            {
                environment["PATH"] = gitBin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH");
                environment["CONTRACT_REAL_GIT"] = realGit!;
                environment["CONTRACT_GIT_CALLS"] = GitCallsPath;
            }
            return Run("/bin/bash", ["tools/scripts/preflight.sh"], environment);
        }
        internal string[] Calls() => TemporaryFileSystem.File.Exists(CallsPath) ? TemporaryFileSystem.File.ReadAllText(CallsPath).Split('\n', StringSplitOptions.RemoveEmptyEntries) : [];
        internal string[] GitCalls() => TemporaryFileSystem.File.Exists(GitCallsPath) ? TemporaryFileSystem.File.ReadAllText(GitCallsPath).Split('\n', StringSplitOptions.RemoveEmptyEntries) : [];
        private (int Exit, string Text, string Error) Run(string executable, string[] args, Dictionary<string, string>? environment = null)
        {
            var start = new ProcessStartInfo(executable) { WorkingDirectory = Root, RedirectStandardOutput = true, RedirectStandardError = true };
            foreach (var arg in args) start.ArgumentList.Add(arg);
            // Synthetic repositories must not inherit the caller workflow's
            // fixed-candidate contract. Tests opt into an event explicitly.
            start.Environment["GITHUB_EVENT_NAME"] = "";
            start.Environment["CANDIDATE_SHA"] = "";
            start.Environment["CI_WORKFLOW_INPUTS"] = "null";
            foreach (var pair in environment ?? []) start.Environment[pair.Key] = pair.Value;
            using var process = Process.Start(start)!;
            var stdout = process.StandardOutput.ReadToEndAsync(); var stderr = process.StandardError.ReadToEndAsync();
            Assert.True(process.WaitForExit(30_000), "process exceeded fixture timeout");
            var error = stderr.GetAwaiter().GetResult();
            return (process.ExitCode, stdout.GetAwaiter().GetResult() + error, error);
        }
        public void Dispose() => TemporaryFileSystem.Directory.Delete(scratch, recursive: true);
    }
}
