using System.Globalization;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeContentChecksScriptTests
{
    private const string KatexPath = "tools/StrataLint.Scribe/Vendor/Katex/katex.min.js";

    [Theory]
    [InlineData(0)]
    [InlineData(29)]
    public void KatexDeltaSelectsScribeChecksAndPropagatesFailure(int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        var unchanged = fixture.RunGate(childExit);
        Assert.Equal(0, unchanged.ExitCode);
        Assert.Empty(fixture.Invocations);

        fixture.Change(KatexPath);
        var result = fixture.RunGate(childExit);

        Assert.Equal(childExit, result.ExitCode);
        Assert.Equal(childExit == 0 ? new[] { "projections", "describe-report" } : ["projections"],
            fixture.Invocations);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(29)]
    public void CacheFetcherDeltaSelectsScribeChecksAndPropagatesFailure(int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();

        var unchanged = fixture.RunGate(childExit);
        Assert.Equal(0, unchanged.ExitCode);
        Assert.Empty(fixture.Invocations);

        fixture.ChangeFetcher();
        var result = fixture.RunGate(childExit);

        Assert.Equal(childExit, result.ExitCode);
        Assert.Equal(
            childExit == 0 ? new[] { "projections", "describe-report" } : ["projections"],
            fixture.Invocations);
    }

    [Theory]
    [InlineData("tools/lean-inspector/Registry.lean", "projections,describe-report")]
    [InlineData("tools/lean-inspector/README.md", "")]
    [InlineData("tools/StrataLint.Scribe/Vendor/Katex/README.md", "")]
    [InlineData(KatexPath, "projections,describe-report")]
    [InlineData("tools/lean-inspector/Census/resources.py", "")]
    [InlineData("Golden/Projection/fixture.json", "projections")]
    [InlineData("Blueprint/D5/fixture.scribe.cs", "describe-report,markdown-check")]
    [InlineData("Blueprint/D5/fixture.md", "markdown-check")]
    [InlineData("Library/Test/note.md", "describe-report")]
    [InlineData("registered.data", "projections,describe-report")]
    public void DeclaredImpactSelectsOnlyItsChecks(string path, string expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        fixture.Change(path);
        var result = fixture.RunGate(0);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(expected.Split(',', StringSplitOptions.RemoveEmptyEntries), fixture.Invocations);
        if (expected.Contains("markdown-check", StringComparison.Ordinal))
            Assert.Equal(Encoding.UTF8.GetBytes(path + "\0"), fixture.MarkdownInput);
    }

    [Theory]
    [InlineData("missing-scope", "scribe-projections")]
    [InlineData("duplicate-scope", "scribe-projections")]
    [InlineData("missing-input", "required.data")]
    [InlineData("duplicate-input", "registered.data")]
    public void RegistrationDefectsStopScribeBeforeDispatch(string defect, string expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        fixture.BreakRegistration(defect);
        fixture.Change("tools/lean-inspector/Registry.lean");
        var result = fixture.RunGate(0);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains(expected, Encoding.UTF8.GetString(result.StandardError));
        Assert.Empty(fixture.Invocations);
    }

    [Theory]
    [InlineData("delete")]
    [InlineData("rename")]
    [InlineData("staged")]
    public void MarkdownDiffKeepsDeletedRenamedAndStagedPaths(string change)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        var paths = fixture.ChangeMarkdown(change);
        var result = fixture.RunGate(0);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(["markdown-check"], fixture.Invocations);
        Assert.Equal(paths, Encoding.UTF8.GetString(fixture.MarkdownInput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries).Order(StringComparer.Ordinal));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class ScribeContentFixture : IDisposable
    {
        private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
        private const string ContentChecksPath = "tools/scripts/workflow/scribe-content-checks.sh";
        private const string CacheInputPath = "tools/scripts/worktree/lean-cache-input.sh";
        private const string CacheFetcherPath = "tools/scripts/worktree/lean-cache-publish.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string bin;
        private readonly string log;
        private readonly string report;
        private readonly string baseline;

        internal ScribeContentFixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            bin = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "scribe.log");
            report = Path.Combine(temporary.Path, "raw-lean-report.json");
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.WriteScratchText(report, "{}\n");
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), InputHelperPath), Path.Combine(repository, InputHelperPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), ContentChecksPath), Path.Combine(repository, ContentChecksPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), CacheInputPath), Path.Combine(repository, CacheInputPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), CacheFetcherPath), Path.Combine(repository, CacheFetcherPath));
            Write("tools/lean-inspector/Registry.lean", "def fixture := 1\n");
            Write("Blueprint/D5/old file.md", "text\n");
            Write("required.data", "required input\n");
            Write("registered.data", "declared input\n");
            Write(KatexPath, "// embedded runtime fixture\n");
            WriteRegistration();
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(bin, "dotnet"), """
                if [[ "$1" == scribe-fixture ]]; then
                  printf '%s\n' "$2" >> "$SCRIBE_LOG"
                  if [[ "$2" == markdown-check ]]; then cat > "$SCRIBE_LOG.paths"; fi
                  exit "$SCRIBE_EXIT"
                fi
                # Transport to the candidate CLI; selection and diagnostics are native.
                while [[ $# -gt 0 && "$1" != -- ]]; do shift; done
                [[ $# -gt 0 ]] || exit 2
                shift
                PATH="$ORIGINAL_PATH" exec dotnet "$NATIVE_CLI" "$@"
                """);
            RunGit("init", "--quiet");
            RunGit("config", "user.email", "stratalint@example.invalid");
            RunGit("config", "user.name", "StrataLint Tests");
            RunGit("add", ".");
            RunGit("commit", "--quiet", "-m", "scribe input fixture");
            baseline = RunGit("rev-parse", "HEAD").Trim();
        }

        private static object Input(string pattern, int minimum = 0) => new
            { patterns = new[] { pattern }, exclude = Array.Empty<string>(), optional_root = (string?)null, min_matches = minimum };

        private void WriteRegistration()
        {
            Write("Meta/FILEMAP.toml", """
                schema_version = 2
                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-tools"
                known_violation_count = 0
                status = "closed"
                [[files]]
                pattern = "Meta/LeanInputs.json"
                kind = "program"
                admission_plane = "judge"
                produced_by = "none"
                consumed_by = ["LeanInputManifest"]
                verified_by = ["LeanInputManifest"]
                artifact_id = "LeanInputManifest"
                runtime_disposition = "committed-source"
                """ + "\n");
            object Scope(string name, string[] includes, params object[] inputs) => new { name, includes, inputs };
            Write("Meta/LeanInputs.json", JsonSerializer.Serialize(new
            {
                schema_version = 1,
                scopes = new[]
                {
                    Scope("scribe-producer", [], Input(CacheFetcherPath, 1), Input("required.data", 1),
                        Input("registered.data", 1), Input("tools/lean-inspector/**/*.lean", 1), Input(KatexPath, 1)),
                    Scope("scribe-projections", ["scribe-producer"], Input("Golden/Projection/*.json")),
                    Scope("scribe-describe", ["scribe-producer"], Input("Blueprint/**/*.scribe.cs"), Input("Library/**/*.md")),
                    Scope("scribe-markdown", [], Input("Blueprint/**/*.scribe.cs"), Input("Blueprint/**/*.md")),
                },
            }) + "\n");
        }

        internal byte[] MarkdownInput => TemporaryFileSystem.File.ReadAllBytes(log + ".paths");

        internal void Change(string path) => Write(path, "changed fixture input\n");

        internal string[] ChangeMarkdown(string change)
        {
            const string oldPath = "Blueprint/D5/old file.md";
            if (change == "delete") RunGit("rm", "--", oldPath);
            else if (change == "rename") RunGit("mv", "--", oldPath, "Blueprint/D5/new file.md");
            else { Change(oldPath); RunGit("add", "--", oldPath); }
            return change == "rename" ? ["Blueprint/D5/new file.md", oldPath] : [oldPath];
        }

        internal void BreakRegistration(string defect)
        {
            if (defect == "missing-input")
            {
                ScriptHarnessScratch.DeleteScratchFile(Path.Combine(repository, "required.data"));
                return;
            }
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(repository, "Meta/LeanInputs.json")))!;
            var scopes = manifest["scopes"]!.AsArray();
            var scope = scopes.Single(item => item!["name"]!.GetValue<string>() == "scribe-projections")!;
            if (defect == "missing-scope") scopes.Remove(scope);
            else if (defect == "duplicate-scope") scopes.Add(scope.DeepClone());
            else scope["inputs"]!.AsArray().Add(JsonSerializer.SerializeToNode(Input("registered.data")));
            Write("Meta/LeanInputs.json", manifest.ToJsonString() + "\n");
        }

        internal string[] Invocations => ScriptHarnessScratch.ReadRecordedCalls(log);

        internal void ChangeFetcher() => ScriptHarnessScratch.AppendScratchText(
            Path.Combine(repository, CacheFetcherPath), "# fetch acceptance changed\n");

        internal ProcessOutput RunGate(int childExit) => TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "ORIGINAL_PATH=\"$PATH\" PATH=\"$1:$PATH\" SCRIBE_LOG=\"$2\" "
                + "SCRIBE_EXIT=\"$3\" STRATALINT_SCRIBE_BASE=\"$6\" NATIVE_CLI=\"$7\" "
                + "exec /bin/bash \"$4\" \"$5\" scribe-fixture",
                "scribe-fetcher-delta", bin, log, childExit.ToString(CultureInfo.InvariantCulture),
                Path.Combine(repository, ContentChecksPath), report, baseline,
                Path.Combine(AppContext.BaseDirectory, "StrataLint.dll")],
            repository, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        private string RunGit(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, repository,
                TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput);
        }

        private void Write(string relativePath, string contents)
        {
            var path = Path.Combine(repository, relativePath);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteScratchText(path, contents);
        }

        public void Dispose() => temporary.Dispose();
    }
}
