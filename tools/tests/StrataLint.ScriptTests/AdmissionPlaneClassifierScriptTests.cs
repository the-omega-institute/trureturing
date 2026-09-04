using System.Text;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Tests;

public sealed class AdmissionPlaneClassifierScriptTests
{
    private static readonly UTF8Encoding Utf8 = new(false);
    private static string CiPath => ".github/" + "work" + "flows/ci.yml";

    [Fact]
    public void JudgeOnlyDeltaIsAccepted()
    {
        var result = RunClassifier(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "tools/change.cs");

        AssertAccepted(result, "status=judge-only judge=1 content=0");
        Assert.Equal("plane=judge-only\n", result.GitHubOutput);
    }

    [Fact]
    public void ContentOnlyDeltaIsAccepted()
    {
        var result = RunClassifier(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "docs/change.md");

        AssertAccepted(result, "status=content-only judge=0 content=1");
        Assert.Equal("plane=content-only\n", result.GitHubOutput);
    }

    [Fact]
    public void EmptyDeltaIsAccepted()
    {
        var result = RunClassifier("this is not TOML");

        AssertAccepted(result, "status=empty judge=0 content=0");
        Assert.Equal("plane=empty\n", result.GitHubOutput);
    }

    [Fact]
    public void MixedDeltaIsRejected()
    {
        var result = RunClassifier(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "tools/change.cs",
            "docs/change.md");

        AssertRejected(result, "status=mixed judge=1 content=1");
    }

    [Fact]
    public void UnmatchedPathIsRejected()
    {
        var result = RunClassifier(Manifest(("docs/**", "content")), "tools/change.cs");

        AssertRejected(result, "reason=path-match-count-not-one");
        Assert.Contains("matches=0", StandardError(result), StringComparison.Ordinal);
    }

    [Fact]
    public void MultiplyMatchedPathIsRejected()
    {
        var result = RunClassifier(
            Manifest(("docs/**", "content"), ("docs/*.md", "content")),
            "docs/change.md");

        AssertRejected(result, "reason=path-match-count-not-one");
        Assert.Contains("matches=2", StandardError(result), StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAdmissionPlaneIsRejected()
    {
        var result = RunClassifier(
            """
            [[files]]
            pattern = "docs/**"

            """,
            "docs/change.md");

        AssertRejected(result, "reason=base-filemap-admission-plane-unavailable");
    }

    [Fact]
    public void MissingPatternIsRejected()
    {
        var result = RunClassifier(
            """
            [[files]]
            admission_plane = "content"

            """,
            "docs/change.md");

        AssertRejected(result, "reason=base-filemap-pattern-unavailable");
    }

    [Fact]
    public void InvalidAdmissionPlaneIsRejected()
    {
        var result = RunClassifier(Manifest(("docs/**", "observer")), "docs/change.md");

        AssertRejected(result, "reason=base-filemap-admission-plane-unavailable");
    }

    [Fact]
    public void MalformedTomlContentDeltaIsRejected()
    {
        var result = RunClassifier("[", "docs/change.md");

        AssertRejected(result, "reason=base-filemap-parse-failed");
        Assert.DoesNotContain("self-repair=bootstrap", StandardError(result), StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedTomlRepairDeltaBootstraps()
    {
        var result = RunClassifier("[", "Meta/FILEMAP.toml");

        AssertAccepted(result, "reason=base-filemap-parse-failed self-repair=bootstrap");
        Assert.Equal("plane=bootstrap\n", result.GitHubOutput);
    }

    [Fact]
    public void MissingBaseFileMapRepairDeltaBootstraps()
    {
        var result = RunClassifier(
            "unused",
            fileMapFetched: false,
            "Meta/FILEMAP.toml");

        AssertAccepted(result, "reason=base-filemap-unavailable self-repair=bootstrap");
        Assert.Equal("plane=bootstrap\n", result.GitHubOutput);
    }

    [Fact]
    public void RepairDeltaWithJudgeReservedPathsUsesTheNarrowClaim()
    {
        var result = RunClassifier(
            Manifest((CiPath, "judge"), ("Meta/FILEMAP.toml", "judge")),
            "Meta/FILEMAP.toml");

        AssertAccepted(
            result,
            "status=judge-only judge=1 content=0 self-repair=reserved-paths-judge");
    }

    [Fact]
    public void QuestionMarkInBasePatternFailsClosed()
    {
        var result = RunClassifier(
            Manifest(("docs/?.md", "content")),
            "docs/a.md");

        AssertRejected(result, "reason=base-filemap-pattern-unsafe");
        Assert.Contains("docs/?.md", StandardError(result), StringComparison.Ordinal);
    }

    [Fact]
    public void RepairDeltaWhoseReservedPathIsContentIsRejected()
    {
        var result = RunClassifier(
            Manifest((CiPath, "judge"), ("Meta/FILEMAP.toml", "content")),
            "Meta/FILEMAP.toml");

        AssertRejected(result, "reason=self-repair-path-not-judge");
    }

    [Theory]
    [InlineData("*.md", "README.md")]
    [InlineData("*.md", "README.md.bak")]
    [InlineData("*.md", "docs/README.md")]
    [InlineData("docs/*.md", "docs/readme.md")]
    [InlineData("docs/*.md", "docs/nested/readme.md")]
    [InlineData("docs/**", "docs/a/b.md")]
    [InlineData("foo**bar", "fooa/bbar")]
    [InlineData("literal.[x]", "literal.[x]")]
    [InlineData("literal.[x]", "literal.ax")]
    [InlineData("**/*.lean", "A.lean")]
    [InlineData("**/*.lean", "D5/A.lean")]
    [InlineData("a*b", "xa-value-b")]
    [InlineData("a*b", "a-value-b")]
    [InlineData("x/*.txt", "x/\U0001F600.txt")]
    [InlineData("x/**", "x/\U0001F600.txt")]
    public void FileMapGlobMatchesCanonicalImplementation(string pattern, string path)
    {
        var canonicalMatch = FileMapGlob.Create(pattern).IsMatch(path);
        var result = RunClassifier(Manifest((pattern, "content")), path);

        Assert.Equal(canonicalMatch ? 0 : 1, result.ExitCode);
    }

    private static ClassifierResult RunClassifier(string manifest, params string[] changedPaths)
    {
        return RunClassifier(manifest, fileMapFetched: true, changedPaths);
    }

    private static ClassifierResult RunClassifier(
        string manifest,
        bool fileMapFetched,
        params string[] changedPaths)
    {
        using var temporary = new TemporaryDirectory();
        var deltaPath = Path.Combine(temporary.Path, "delta.z");
        var manifestPath = Path.Combine(temporary.Path, "FILEMAP.toml");
        var githubOutputPath = Path.Combine(temporary.Path, "github-output");
        var delta = changedPaths.Length == 0
            ? []
            : Utf8.GetBytes(string.Join('\0', changedPaths) + "\0");
        File.WriteAllBytes(deltaPath, delta);
        File.WriteAllText(manifestPath, manifest, Utf8);

        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            [
                "LC_ALL=C",
                "PYTHONHASHSEED=0",
                "python3.12",
                Path.Combine(AppContext.BaseDirectory, "admission-plane-classify.py"),
                "--delta-file",
                deltaPath,
                "--filemap",
                manifestPath,
                "--filemap-fetched",
                fileMapFetched ? "true" : "false",
                "--github-output",
                githubOutputPath,
            ],
            temporary.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        var githubOutput = ScriptHarnessScratch.ReadScratchText(temporary, "github-output");
        return new ClassifierResult(process, githubOutput);
    }

    private static void AssertAccepted(ClassifierResult result, string outputFragment)
    {
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        Assert.Contains(outputFragment, StandardOutput(result), StringComparison.Ordinal);
    }

    private static void AssertRejected(ClassifierResult result, string errorFragment)
    {
        Assert.True(result.ExitCode != 0, Diagnostics(result));
        Assert.Empty(result.StandardOutput);
        Assert.Empty(result.GitHubOutput);
        Assert.Contains(errorFragment, StandardError(result), StringComparison.Ordinal);
    }

    private static string Manifest(params (string Pattern, string Plane)[] entries)
    {
        var builder = new StringBuilder();
        foreach (var entry in entries)
        {
            builder.Append("[[files]]\npattern = ")
                .Append(System.Text.Json.JsonSerializer.Serialize(entry.Pattern))
                .Append("\nadmission_plane = ")
                .Append(System.Text.Json.JsonSerializer.Serialize(entry.Plane))
                .Append("\n\n");
        }

        return builder.ToString();
    }

    private static string StandardOutput(ClassifierResult result) =>
        Utf8.GetString(result.StandardOutput);

    private static string StandardError(ClassifierResult result) =>
        Utf8.GetString(result.StandardError);

    private static string Diagnostics(ClassifierResult result) =>
        "stdout:\n" + StandardOutput(result) + "\nstderr:\n" + StandardError(result);

    private sealed record ClassifierResult(ProcessOutput Process, string GitHubOutput)
    {
        internal int ExitCode => Process.ExitCode;
        internal byte[] StandardOutput => Process.StandardOutput;
        internal byte[] StandardError => Process.StandardError;
    }
}
