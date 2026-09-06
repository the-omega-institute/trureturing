using System.Diagnostics;
using System.Globalization;
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
    [InlineData("GIT_DIR")]
    [InlineData("GIT_CONFIG")]
    [InlineData("GIT_OBJECT_DIRECTORY")]
    [InlineData("GIT_TEMPLATE_DIR")]
    [InlineData("GIT_ALTERNATE_OBJECT_DIRECTORIES")]
    [InlineData("GIT_CEILING_DIRECTORIES")]
    [InlineData("GIT_NAMESPACE")]
    [InlineData("GIT_FUTURE_FIXTURE_REDIRECT")]
    public void FixtureRejectsInheritedGitEnvironment(string variable)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
        {
            using var fixture = new AtomHistoryRepository(["PATH", variable, "HOME"]);
        });
        Assert.Contains(variable, exception.Message);
    }

    [Fact]
    public void FixtureWritesStayInsideTemporaryRoot() => AssertInheritedConfigurationIsolation();

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

        var isolationChild = configuration == "inherited-config-redirections";
        if (isolationChild)
        {
            var exception = Assert.Throws<InvalidOperationException>(() =>
                AtomHistoryRepository.RejectInheritedGitEnvironment(
                    Environment.GetEnvironmentVariables().Keys.Cast<string>()));
            Assert.Contains("GIT_OBJECT_DIRECTORY", exception.Message);
            Assert.Contains("GIT_TEMPLATE_DIR", exception.Message);
        }

        // Only this isolated child injects the clean preflight snapshot to exercise the
        // fixture's whitelist while its actual process environment remains poisoned.
        using var fixture = new AtomHistoryRepository(isolationChild ? [] : null);
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

        if (isolationChild)
        {
            foreach (var variable in Environment.GetEnvironmentVariables().Keys.Cast<string>()
                .Where(variable => variable.StartsWith("GIT_", StringComparison.OrdinalIgnoreCase)).ToArray())
                Environment.SetEnvironmentVariable(variable, null);
            Environment.SetEnvironmentVariable("HOME", fixture.Home);
            Assert.Empty(Directory.CreateDirectory(fixture.Home).EnumerateFileSystemInfos());
        }

        var history = fixture.ReadUnchanged(fixture.Root);
        if (isolationChild)
            Assert.Empty(Directory.CreateDirectory(fixture.Home).EnumerateFileSystemInfos());

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
        var objects = Path.Combine(temporary.Path, "outside-objects");
        var templates = Path.Combine(temporary.Path, "outside-templates");
        Directory.CreateDirectory(objects);
        Directory.CreateDirectory(templates);
        var bytes = Encoding.UTF8.GetBytes("[user]\n\tname = Outside Fixture\n"
            + "\temail = outside@example.invalid\n[fixture]\n\tuntouched = true\n");
        foreach (var path in new[] { config, global, system }) File.WriteAllBytes(path, bytes);

        var result = TestProcessRunner.Run("/usr/bin/env",
            ["-i", $"PATH={Environment.GetEnvironmentVariable("PATH")}",
                $"HOME={temporary.Path}", $"TMPDIR={temporary.Path}", "LC_ALL=C", "LANG=C",
                $"GIT_CONFIG={config}", $"GIT_CONFIG_GLOBAL={global}", $"GIT_CONFIG_SYSTEM={system}",
                $"GIT_OBJECT_DIRECTORY={objects}", $"GIT_TEMPLATE_DIR={templates}",
                "GIT_CONFIG_NOSYSTEM=0", "STRATALINT_ATOM_HISTORY_CONFIG_CHILD=1",
                "dotnet", "vstest", Path.Combine(AppContext.BaseDirectory, "StrataLint.ScriptTests.dll"),
                "--TestCaseFilter:DisplayName~ReaddedMergeAtomRetainsSideBranchCommitterTimeAcrossGitConfig&DisplayName~inherited-config-redirections",
                "--Logger:trx;LogFileName=child.trx", $"--ResultsDirectory:{temporary.Path}"],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        foreach (var path in new[] { config, global, system }) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Empty(Directory.CreateDirectory(objects).EnumerateFileSystemInfos());
        Assert.Empty(Directory.CreateDirectory(templates).EnumerateFileSystemInfos());
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
        internal TemporaryDirectory Temporary { get; }
        internal string Root { get; }
        internal string Home { get; }
        internal string RootAtomId { get; }
        internal string SideAtomId { get; }

        internal AtomHistoryRepository(IEnumerable<string>? inheritedVariables = null)
        {
            RejectInheritedGitEnvironment(inheritedVariables
                ?? Environment.GetEnvironmentVariables().Keys.Cast<string>());
            Temporary = new TemporaryDirectory();
            Root = Path.Combine(Temporary.Path, "repository");
            Home = Path.Combine(Temporary.Path, "home");
            Directory.CreateDirectory(Home);
            Directory.CreateDirectory(Root);
            var template = Path.Combine(Temporary.Path, "empty-template");
            Directory.CreateDirectory(template);
            // An empty repository skeleton makes the first Git call a location check,
            // before init or any other Git command can write fixture state.
            Directory.CreateDirectory(Path.Combine(Root, ".git", "objects"));
            Directory.CreateDirectory(Path.Combine(Root, ".git", "refs"));
            File.WriteAllText(Path.Combine(Root, ".git", "HEAD"), "ref: refs/heads/main\n");
            Assert.Equal(Path.Combine(Root, ".git"),
                Path.GetFullPath(Git("rev-parse", "--git-dir").Trim(), Root));
            Git("init", $"--template={template}", "--initial-branch=main");
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

        internal static void RejectInheritedGitEnvironment(IEnumerable<string> variables)
        {
            var inherited = variables
                .Where(variable => variable.StartsWith("GIT_", StringComparison.OrdinalIgnoreCase))
                .Order(StringComparer.Ordinal).ToArray();
            if (inherited.Length != 0)
                throw new InvalidOperationException("Synthetic git fixture requires unset variables: "
                    + string.Join(", ", inherited));
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
            Git("-c", $"{key}={value}", "config", "--file", Path.Combine(Root, ".git", "config"), key, value);

        internal string GitAt(string checkout, params string[] arguments) =>
            Run(arguments, checkout);

        private void GitAtDate(string date, params string[] arguments)
        {
            Git(arguments);
            var tree = Git("show", "-s", "--format=%T", "HEAD").Trim();
            var parents = Git("show", "-s", "--format=%P", "HEAD")
                .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
            var message = Git("show", "-s", "--format=%B", "HEAD");
            var timestamp = DateTimeOffset.Parse(date, CultureInfo.InvariantCulture)
                .ToUnixTimeSeconds().ToString(CultureInfo.InvariantCulture);
            var identity = $"Atom History Fixture <atom-history@example.invalid> {timestamp} +0000";
            // Git has no command-line committer-date option. Write a canonical commit
            // object with explicit dates, retaining the real commit's tree and parents.
            var commit = $"tree {tree}\n" + string.Concat(parents.Select(parent => $"parent {parent}\n"))
                + $"author {identity}\ncommitter {identity}\n\n{message}";
            var oid = Run(["hash-object", "-t", "commit", "-w", "--stdin"], Root, commit).Trim();
            Git("update-ref", "HEAD", oid);
        }

        private string Run(string[] arguments, string checkout, string? standardInput = null)
        {
            var start = new ProcessStartInfo("git")
            {
                WorkingDirectory = checkout,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                RedirectStandardInput = standardInput is not null,
            };
            start.Environment.Clear();
            start.Environment["PATH"] = Environment.GetEnvironmentVariable("PATH");
            start.Environment["HOME"] = Home;
            start.Environment["TMPDIR"] = Temporary.Path;
            start.Environment["LC_ALL"] = "C";
            start.Environment["LANG"] = "C";
            foreach (var argument in new[] { "-C", checkout, "-c", "core.hooksPath=/dev/null",
                "-c", "commit.gpgsign=false", "-c", "gc.auto=0" }.Concat(arguments))
                start.ArgumentList.Add(argument);
            var result = TestProcessRunner.Classify(() => RunProcess(start, standardInput), "git");
            Assert.True(result.ExitCode == 0, $"git exited {result.ExitCode}: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }

        private static ProcessOutput RunProcess(ProcessStartInfo start, string? standardInput)
        {
            using var process = Process.Start(start)
                ?? throw new InvalidOperationException("Could not start fixture git");
            using var cancellation = new CancellationTokenSource(TestBudgets.ScriptProcessHangGuard);
            try
            {
                var output = process.StandardOutput.ReadToEndAsync(cancellation.Token);
                var error = process.StandardError.ReadToEndAsync(cancellation.Token);
                if (standardInput is not null)
                {
                    process.StandardInput.Write(standardInput);
                    process.StandardInput.Close();
                }
                process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
                return new ProcessOutput(process.ExitCode,
                    Encoding.UTF8.GetBytes(output.GetAwaiter().GetResult()),
                    Encoding.UTF8.GetBytes(error.GetAwaiter().GetResult()));
            }
            catch (OperationCanceledException exception)
            {
                process.Kill(entireProcessTree: true);
                throw new TimeoutException("Fixture git exceeded its infrastructure hang guard", exception);
            }
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
