using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryIngestClosureScriptTests
{
    [Fact]
    public void CleanCandidateExitsZero()
    {
        using var fixture = new TheoryIngestClosureFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void DirtyHarnessPathFailsAndNamesExactPath()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.Write("Meta/StrataLint/judge.sh", "judge");
        fixture.Write("Makefile", "judge");
        fixture.Write("global.json", "{\"judge\":true}\n");

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "Meta/StrataLint/judge.sh",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void DirtyTheoryLedgerFailsAndNamesExactPath()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.Write("docs/develop/theory/volume/source.toml", "updated");

        var result = fixture.Run();
        var stderr = Encoding.UTF8.GetString(result.StandardError);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("THEORY-INGEST-CLOSURE-001", stderr, StringComparison.Ordinal);
        Assert.Contains("docs/develop/theory/volume/source.toml", stderr, StringComparison.Ordinal);
    }

    private sealed class TheoryIngestClosureFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();

        internal TheoryIngestClosureFixture()
        {
            RunGit("init", "-q");
            RunGit("config", "user.email", "test@example.com");
            RunGit("config", "user.name", "test");
            Write("Meta/StrataLint/judge.sh", "base");
            Write("Makefile", "base");
            Write("global.json", "{}");
            Write("docs/develop/theory/volume/theory.md", "# volume\n");
            Write("docs/develop/theory/volume/source.toml", "[source]\nid=\"volume\"\n");
            RunGit("add", ".");
            RunGit("commit", "-qm", "init");
        }

        internal void Write(string relativePath, string contents)
        {
            var path = Path.Combine(repository.Path, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        internal ProcessOutput Run()
        {
            var script = Path.Combine(
                PrOpenScriptTests.RepositoryRoot(),
                "Meta", "StrataLint", "scripts", "workflow", "theory-ingest-closure.sh");
            return BoundedProcessRunner.Run(
                "bash",
                [script, repository.Path],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }

        public void Dispose() => repository.Dispose();

        private void RunGit(params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, repository.Path, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
        }
    }
}
