using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PrOpenScriptTests
{
    [Fact]
    public void PrOpenRejectsMissingRequiredArgumentsAndUnreadableBody()
    {
        using var fixture = new PrScriptFixture();

        Assert.Equal(2, fixture.RunOpen("--title", "title").ExitCode);
        Assert.Equal(2, fixture.RunOpen("--head", "branch").ExitCode);
        var unreadable = fixture.RunOpen(
            "--head", "branch", "--title", "title", "--body-file", fixture.MissingBody);

        Assert.Equal(2, unreadable.ExitCode);
        Assert.Contains("body file is not readable", Text(unreadable.StandardError), StringComparison.Ordinal);
        Assert.Empty(fixture.Invocations);
    }

    [Fact]
    public void PrOpenCreatesAndArmsPullRequestWithTokenIsolation()
    {
        using var fixture = new PrScriptFixture();

        var result = fixture.RunOpen("--head", "topic", "--title", "A title");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("42\n", Text(result.StandardOutput));
        Assert.Equal(
            [
                "pr create --repo owner/repo --base dev --head topic --title A title --fill-first|token=app-token",
                "pr merge 42 --repo owner/repo --auto --merge|token=none",
            ],
            fixture.Invocations);
        Assert.DoesNotContain("update-branch", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void PrOpenPassesReadableBodyFileToCreate()
    {
        using var fixture = new PrScriptFixture();
        File.WriteAllText(fixture.Body, "body\n", new UTF8Encoding(false));

        var result = fixture.RunOpen(
            "--head", "topic", "--title", "title", "--body-file", fixture.Body);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains($"--body-file {fixture.Body}|token=app-token", fixture.Invocations[0], StringComparison.Ordinal);
    }

    [Fact]
    public void PrOpenCreateFailureDoesNotCloseAnything()
    {
        using var fixture = new PrScriptFixture { FailStep = "create" };

        var result = fixture.RunOpen("--head", "topic", "--title", "title");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Single(fixture.Invocations);
        Assert.DoesNotContain(fixture.Invocations, line => line.Contains("pr close", StringComparison.Ordinal));
    }

    [Fact]
    public void PrOpenAutoMergeFailureIsFatal()
    {
        using var fixture = new PrScriptFixture { FailStep = "merge" };

        var result = fixture.RunOpen("--head", "topic", "--title", "title");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(2, fixture.Invocations.Count);
        Assert.Contains("step=auto-merge", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void PrOpenFallsBackToLocalGhWhenAppTokenFails()
    {
        using var fixture = new PrScriptFixture { AppTokenFails = true };

        var result = fixture.RunOpen("--head", "topic", "--title", "title");

        Assert.Equal(0, result.ExitCode);
        Assert.EndsWith("|token=none", fixture.Invocations[0], StringComparison.Ordinal);
    }

    // The tests below inject PR_OPEN_REPO, so nothing here exercises the production
    // default. That default is what the canonical `make pr-open` front gate actually
    // uses, and a wrong value points the whole gate at a repository that does not
    // exist; it shipped wrong once. Pin it against the real remote.
    [Fact]
    public void PrOpenDefaultsToTheRealRepository()
    {
        var script = File.ReadAllText(
            Path.Combine(RepositoryRoot(), "tools", "scripts", "pr.sh"),
            Encoding.UTF8);

        Assert.Contains(
            "PR_REPO=\"${PR_OPEN_REPO:-the-omega-institute/trureturing}\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("PR_BASE=\"${PR_OPEN_BASE:-dev}\"", script, StringComparison.Ordinal);
        // Exactly one copy of the address lives in the tool.
        Assert.Equal(1, script.Split("PR_REPO=").Length - 1);
    }

    private static string Text(byte[] bytes) => Encoding.UTF8.GetString(bytes);

    internal static string RepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private sealed class PrScriptFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string bin;
        private readonly string invocations;

        internal PrScriptFixture()
        {
            bin = Path.Combine(temporary.Path, "bin");
            invocations = Path.Combine(temporary.Path, "gh-invocations");
            Directory.CreateDirectory(bin);
            WriteExecutable(Path.Combine(bin, "gh"), FakeGh);
            WriteExecutable(Path.Combine(bin, "gh-app"), FakeGhApp);
        }

        internal string Body => Path.Combine(temporary.Path, "body.md");
        internal string MissingBody => Path.Combine(temporary.Path, "missing.md");
        internal string FailStep { get; set; } = "";
        internal bool AppTokenFails { get; set; }
        internal IReadOnlyList<string> Invocations =>
            File.Exists(invocations) ? File.ReadAllLines(invocations) : [];

        internal ProcessOutput RunOpen(params string[] arguments) =>
            Run([.. new[] { "open" }, .. arguments]);

        public void Dispose() => temporary.Dispose();

        private ProcessOutput Run(string[] arguments)
        {
            var script = Path.Combine(FindRepositoryRoot(), "tools", "scripts", "pr.sh");
            return BoundedProcessRunner.Run(
                "env",
                [
                    "-u", "GH_TOKEN",
                    $"PATH={bin}:/usr/bin:/bin:/usr/sbin:/sbin",
                    "PR_OPEN_REPO=owner/repo",
                    "PR_OPEN_BASE=dev",
                    "PR_OPEN_TIMEOUT_SECONDS=5",
                    $"PR_TEST_INVOCATIONS={invocations}",
                    $"PR_TEST_FAIL_STEP={FailStep}",
                    $"PR_TEST_APP_FAIL={(AppTokenFails ? "1" : "0")}",
                    "bash", script,
                    .. arguments,
                ],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }

        private void WriteExecutable(string path, string contents)
        {
            File.WriteAllText(path, contents, new UTF8Encoding(false));
            var chmod = BoundedProcessRunner.Run(
                "chmod", ["+x", path], temporary.Path, TimeSpan.FromSeconds(30), 4096);
            Assert.Equal(0, chmod.ExitCode);
        }

        private static string FindRepositoryRoot() => PrOpenScriptTests.RepositoryRoot();

        private const string FakeGh = """
            #!/usr/bin/env bash
            set -euo pipefail
            token="${GH_TOKEN:-none}"
            printf '%s|token=%s\n' "$*" "$token" >> "$PR_TEST_INVOCATIONS"
            case " $* " in
              *" pr create "*)
                [[ "$PR_TEST_FAIL_STEP" != create ]] || exit 41
                printf '%s\n' 'https://github.com/owner/repo/pull/42'
                ;;
              *" pr merge "*)
                [[ "$PR_TEST_FAIL_STEP" != merge ]] || exit 42
                ;;
            esac
            """;

        private const string FakeGhApp = """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "${PR_TEST_APP_FAIL:-0}" != 1 ]] || exit 44
            printf '%s\n' 'app-token'
            """;
    }
}
