using System.Text;
using System.Xml.Linq;
using StrataLint.Cli;
using StrataLint.Engine;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class GitAtomHistorySourceTests
{
    [Theory]
    [InlineData("default")]
    [InlineData("diff-merges-off")]
    [InlineData("show-root-false")]
    [InlineData("both-disabled")]
    [InlineData("first-parent")]
    [InlineData("inherited-config-redirections")]
    public void ReaddedMergeAtomRetainsSideBranchCommitterTimeAcrossGitConfig(string configuration)
    {
        if (configuration == "inherited-config-redirections"
            && Environment.GetEnvironmentVariable("STRATALINT_ATOM_HISTORY_CONFIG_CHILD") != "1")
        {
            AssertInheritedConfigurationIsolation();
            return;
        }

        using var fixture = new AtomHistoryRepository();
        if (configuration == "inherited-config-redirections")
        {
            Assert.Equal("Atom History Fixture", fixture.Git("config", "--file",
                Path.Combine(fixture.Root, ".git", "config"), "--get", "user.name").Trim());
            Assert.Equal("atom-history@example.invalid", fixture.Git("config", "--file",
                Path.Combine(fixture.Root, ".git", "config"), "--get", "user.email").Trim());
            Assert.Equal("Atom History Fixture", fixture.Git("config", "--get", "user.name").Trim());
        }
        if (configuration is "diff-merges-off" or "both-disabled")
            fixture.Configure("log.diffMerges", "off");
        if (configuration is "first-parent")
            fixture.Configure("log.diffMerges", "first-parent");
        if (configuration is "show-root-false" or "both-disabled" or "first-parent")
            fixture.Configure("log.showRoot", "false");

        var history = fixture.ReadUnchanged(fixture.Root);

        Assert.False(history.IsShallow);
        Assert.True(history.FirstAdded.TryGetValue(fixture.SideAtomId, out var side), configuration);
        Assert.Equal(new DateTimeOffset(2026, 8, 14, 0, 0, 0, TimeSpan.Zero), side);
        Assert.True(history.FirstAdded.TryGetValue(fixture.RootAtomId, out var root), configuration);
        Assert.Equal(new DateTimeOffset(2026, 8, 1, 0, 0, 0, TimeSpan.Zero), root);
    }

    private static void AssertInheritedConfigurationIsolation()
    {
        using var temporary = new TemporaryDirectory();
        var config = Path.Combine(temporary.Path, "redirect.config");
        var global = Path.Combine(temporary.Path, "global.config");
        var system = Path.Combine(temporary.Path, "system.config");
        var bytes = Encoding.UTF8.GetBytes("[user]\n\tname = Outside Fixture\n"
            + "\temail = outside@example.invalid\n[fixture]\n\tuntouched = true\n");
        foreach (var path in new[] { config, global, system }) File.WriteAllBytes(path, bytes);

        var result = TestProcessRunner.Run("/usr/bin/env",
            ["-u", "GIT_DIR", "-u", "GIT_COMMON_DIR", "-u", "GIT_WORK_TREE", "-u", "GIT_INDEX_FILE",
                $"GIT_CONFIG={config}", $"GIT_CONFIG_GLOBAL={global}", $"GIT_CONFIG_SYSTEM={system}",
                "GIT_CONFIG_NOSYSTEM=0", "STRATALINT_ATOM_HISTORY_CONFIG_CHILD=1",
                "dotnet", "vstest", Path.Combine(AppContext.BaseDirectory, "StrataLint.ScriptTests.dll"),
                "--TestCaseFilter:DisplayName~ReaddedMergeAtomRetainsSideBranchCommitterTimeAcrossGitConfig&DisplayName~inherited-config-redirections",
                "--Logger:trx;LogFileName=child.trx", $"--ResultsDirectory:{temporary.Path}"],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        foreach (var path in new[] { config, global, system }) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
        var report = XDocument.Parse(File.ReadAllText(Path.Combine(temporary.Path, "child.trx")));
        XNamespace ns = "http://microsoft.com/schemas/VisualStudio/TeamTest/2010";
        var test = Assert.Single(report.Descendants(ns + "UnitTestResult"));
        Assert.Equal("Passed", test.Attribute("outcome")?.Value);
        Assert.Contains("inherited-config-redirections", test.Attribute("testName")?.Value);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void DiscoversShallowMetadataInRegularAndLinkedWorktrees(bool shallow, bool linked)
    {
        using var fixture = new AtomHistoryRepository();
        var checkout = fixture.Root;
        if (shallow)
        {
            checkout = Path.Combine(fixture.Temporary.Path, "shallow-clone");
            fixture.Git("clone", "--depth=1", "--no-local", fixture.Root, checkout);
        }

        if (linked)
        {
            var worktree = Path.Combine(fixture.Temporary.Path, "linked-worktree");
            fixture.GitAt(checkout, "worktree", "add", "--detach", worktree, "HEAD");
            checkout = worktree;
            Assert.True(File.Exists(Path.Combine(checkout, ".git")));
            var gitDirectory = fixture.GitAt(checkout, "rev-parse", "--absolute-git-dir").Trim();
            Assert.True(File.Exists(Path.Combine(gitDirectory, "commondir")));
        }
        else
        {
            Assert.True(Directory.Exists(Path.Combine(checkout, ".git")));
        }

        Assert.Equal(shallow ? "true" : "false",
            fixture.GitAt(checkout, "rev-parse", "--is-shallow-repository").Trim());
        var history = fixture.ReadUnchanged(checkout);

        Assert.Equal(shallow, history.IsShallow);
    }

    private sealed class AtomHistoryRepository : IDisposable
    {
        internal TemporaryDirectory Temporary { get; } = new();
        internal string Root { get; }
        internal string RootAtomId { get; }
        internal string SideAtomId { get; }

        internal AtomHistoryRepository()
        {
            foreach (var variable in new[] { "GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE" })
                Assert.True(string.IsNullOrEmpty(Environment.GetEnvironmentVariable(variable)),
                    $"Synthetic git fixture requires {variable} to be unset");
            Root = Path.Combine(Temporary.Path, "repository");
            Directory.CreateDirectory(Root);
            Git("init", "--initial-branch=main");
            Assert.Equal(Path.Combine(Root, ".git"),
                Path.GetFullPath(Git("rev-parse", "--git-dir").Trim(), Root));
            Configure("user.name", "Atom History Fixture");
            Configure("user.email", "atom-history@example.invalid");
            RootAtomId = WriteAtom("root claim\n");
            Commit("2026-08-01T00:00:00Z", "root addition");
            Git("checkout", "-b", "other");
            File.WriteAllText(Path.Combine(Root, "other.txt"), "other parent\n");
            Commit("2026-08-05T00:00:00Z", "other divergence");
            Git("checkout", "main");
            Git("checkout", "-b", "side");
            File.WriteAllText(Path.Combine(Root, "side.txt"), "side parent\n");
            Commit("2026-08-10T00:00:00Z", "side divergence");
            // This add exists only in a merge diff, never in either parent's tree.
            Git("merge", "--no-ff", "--no-commit", "other");
            SideAtomId = WriteAtom("side claim\n");
            Commit("2026-08-14T00:00:00Z", "side merge addition");
            Git("checkout", "main");
            File.WriteAllBytes(Path.Combine(Root, "main.bin"), [0, 255, 13, 10, 128]);
            Commit("2026-08-21T00:00:00Z", "main divergence");
            GitAtDate("2026-09-01T00:00:00Z", "merge", "--no-ff", "--no-gpg-sign",
                "-m", "merge side", "side");
            Git("rm", DigestionCasStore.RootPath + SideAtomId);
            Commit("2026-09-02T00:00:00Z", "delete side atom");
            Assert.Equal(SideAtomId, WriteAtom("side claim\n"));
            Commit("2026-09-03T00:00:00Z", "re-add side atom");
        }

        internal AtomHistory ReadUnchanged(string checkout)
        {
            var paths = GitAt(checkout, "ls-files", "-z")
                .Split('\0', StringSplitOptions.RemoveEmptyEntries);
            var before = paths.ToDictionary(path => path,
                path => File.ReadAllBytes(Path.Combine(checkout, path)), StringComparer.Ordinal);
            try
            {
                return new GitAtomHistorySource(checkout).Read();
            }
            finally
            {
                Assert.Equal(paths, GitAt(checkout, "ls-files", "-z")
                    .Split('\0', StringSplitOptions.RemoveEmptyEntries));
                foreach (var (path, bytes) in before)
                    Assert.Equal(bytes, File.ReadAllBytes(Path.Combine(checkout, path)));
            }
        }

        internal string Git(params string[] arguments) => GitAt(Root, arguments);

        internal void Configure(string key, string value) =>
            Git("config", "--file", Path.Combine(Root, ".git", "config"), key, value);

        internal string GitAt(string checkout, params string[] arguments) =>
            Run(arguments, checkout);

        private void GitAtDate(string date, params string[] arguments) => Run(arguments, Root,
            [$"GIT_AUTHOR_DATE={date}", $"GIT_COMMITTER_DATE={date}"]);

        private static string Run(string[] arguments, string checkout, string[]? environment = null)
        {
            var result = TestProcessRunner.Run("/usr/bin/env",
                ["-u", "GIT_DIR", "-u", "GIT_COMMON_DIR", "-u", "GIT_WORK_TREE", "-u", "GIT_INDEX_FILE",
                    "-u", "GIT_CONFIG",
                    "-u", "GIT_CONFIG_GLOBAL", "-u", "GIT_CONFIG_SYSTEM", "-u", "GIT_CONFIG_NOSYSTEM",
                    "-u", "GIT_CONFIG_PARAMETERS", "-u", "GIT_CONFIG_COUNT",
                    "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null", "GIT_CONFIG_NOSYSTEM=1",
                    .. environment ?? [], "git", "-C", checkout,
                    "-c", "init.templateDir=", "-c", "core.hooksPath=/dev/null",
                    "-c", "commit.gpgsign=false", "-c", "gc.auto=0", .. arguments], checkout,
                TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, $"git exited {result.ExitCode}: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }

        private void Commit(string date, string message)
        {
            Git("add", "--all");
            GitAtDate(date, "commit", "-m", message);
        }

        private string WriteAtom(string content)
        {
            var atom = DigestionCasStore.Capture(Encoding.UTF8.GetBytes(content));
            var path = Path.Combine(Root, atom.RelativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, atom.Bytes.ToArray());
            return atom.Reference["sha256:".Length..];
        }

        public void Dispose() => Temporary.Dispose();
    }
}
