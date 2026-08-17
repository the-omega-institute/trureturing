using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryIngestClosureScriptTests
{
    [Fact]
    public void ProducerNoOpWithoutDeclaredOutputDeltaFailsClosed()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.CommitTheoryChange();

        var result = fixture.Propose();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "THEORY-INGEST-CLOSURE-001",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void BuildSideEffectsOutsideDeclaredWriteSetDoNotAffectProposal()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.CommitTheoryChange();
        fixture.Write("Declared/Output/generated.txt", "trusted output\n");
        fixture.Write("build/noise.txt", "build side effect\n");

        var result = fixture.Propose();
        var patch = fixture.ReadProposal();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("Declared/Output/generated.txt", patch, StringComparison.Ordinal);
        Assert.DoesNotContain("build/noise.txt", patch, StringComparison.Ordinal);
    }

    [Fact]
    public void IgnoredOutputInsideDeclaredWriteSetStillEntersProposal()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.CommitTheoryChange();
        fixture.Write(".gitignore", "Declared/Output/ignored.txt\n");
        fixture.Write("Declared/Output/ignored.txt", "declared ignored output\n");

        var result = fixture.Propose();
        var patch = fixture.ReadProposal();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("Declared/Output/ignored.txt", patch, StringComparison.Ordinal);
    }

    [Fact]
    public void AlreadyClosedCandidateWithDeclaredOutputDeltaProducesCompleteProposal()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.Write("docs/develop/theory/volume/theory.md", "# changed\n");
        fixture.Write("Declared/Output/generated.txt", "closed output\n");
        fixture.Commit("closed candidate");

        var result = fixture.Propose();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("Declared/Output/generated.txt", fixture.ReadProposal(), StringComparison.Ordinal);
    }

    [Fact]
    public void AuthorizedWriteSetIsDerivedFromFileMapProducerDeclaration()
    {
        using var fixture = new TheoryIngestClosureFixture("Different/Declared/**");
        fixture.CommitTheoryChange();
        fixture.Write("Different/Declared/generated.txt", "declared output\n");

        var result = fixture.Propose();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("Different/Declared/generated.txt", fixture.ReadProposal(), StringComparison.Ordinal);
        Assert.Contains(
            "filemap-conform --producer-write-set IngestCommand",
            fixture.ReadDotnetArguments(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ProposalBytesMustExactlyMatchTrustedRecomputationBeforeAuthorization()
    {
        using var fixture = new TheoryIngestClosureFixture();
        var proposal = fixture.WriteExternal("proposal.patch", "candidate bytes\n");
        var trusted = fixture.WriteExternal("trusted.patch", "trusted bytes\n");

        var result = fixture.Authorize(proposal, trusted);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "THEORY-INGEST-CLOSURE-001",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidDeletePatchIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.Delete("Declared/Output/existing.txt");
        var patch = fixture.CapturePatch("HEAD");
        fixture.RunGit("restore", "Declared/Output/existing.txt");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "THEORY-INGEST-CLOSURE-001",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidModeChangePatchIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TheoryIngestClosureFixture();
        fixture.MakeExecutable("Declared/Output/existing.txt");
        var patch = fixture.CapturePatch("HEAD", "Declared/Output");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "THEORY-INGEST-CLOSURE-001",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidBinaryPatchIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.WriteBytes("Declared/Output/existing.txt", [0, 1, 2, 3]);
        var patch = fixture.CapturePatch("HEAD", "Declared/Output");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "binary patches are not authorized",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidPathOutsideFileMapWriteSetIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.Write("Outside/existing.txt", "changed outside\n");
        var patch = fixture.CapturePatch("HEAD", "Outside");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "outside the FILEMAP-derived write set",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void BehindBaseAlreadyClosedCandidateIsAcceptedAndPreservesBaseTheory()
    {
        using var fixture = new TheoryIngestClosureFixture();

        var result = fixture.WritebackBehindBaseAlreadyClosedCandidate();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "candidate head is already closed",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.Equal(
            "# base-only theory\n",
            fixture.Read("docs/develop/theory/base-only/theory.md"));
    }

    [Fact]
    public void WritebackCommitHasExactlyEventHeadAsItsParent()
    {
        using var fixture = new TheoryIngestClosureFixture();

        var transaction = fixture.WritebackWithDeclaredOutputDelta();

        Assert.True(
            transaction.Output.ExitCode == 0,
            $"writeback exited {transaction.Output.ExitCode}\n"
            + $"stdout:\n{Encoding.UTF8.GetString(transaction.Output.StandardOutput)}\n"
            + $"stderr:\n{Encoding.UTF8.GetString(transaction.Output.StandardError)}");
        Assert.Equal(transaction.EventHeadSha, transaction.ParentShas);
    }

    private sealed class TheoryIngestClosureFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();

        private readonly string proposalPath;
        private readonly string dotnetArgumentsPath;
        private readonly string binDirectory;

        internal TheoryIngestClosureFixture(string writePattern = "Declared/Output/**")
        {
            RunGit("init", "-q");
            RunGit("config", "user.email", "test@example.com");
            RunGit("config", "user.name", "test");
            binDirectory = Path.Combine(repository.Path, "test-bin");
            proposalPath = Path.Combine(repository.Path, "proposal", "theory-ingest.patch");
            dotnetArgumentsPath = Path.Combine(repository.Path, "dotnet-arguments.txt");
            Directory.CreateDirectory(binDirectory);
            Write("Declared/Output/existing.txt", "base output\n");
            Write("Outside/existing.txt", "base outside\n");
            Write("docs/develop/theory/volume/theory.md", "# volume\n");
            Write("docs/develop/theory/volume/source.toml", "[source]\nid=\"volume\"\n");
            Write("write-pattern.txt", writePattern + "\n");
            Write("test-bin/dotnet", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$*" >> "$DOTNET_ARGUMENTS_PATH"
                cat "$WRITE_PATTERN_PATH"
                """ + "\n");
            if (!OperatingSystem.IsWindows())
            {
                File.SetUnixFileMode(
                    Path.Combine(binDirectory, "dotnet"),
                    UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            }
            RunGit("add", "Declared", "Outside", "docs");
            RunGit("commit", "-qm", "base");
        }

        internal void Write(string relativePath, string contents)
        {
            var path = Path.Combine(repository.Path, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        internal void Delete(string relativePath) => File.Delete(Path.Combine(repository.Path, relativePath));

        internal void WriteBytes(string relativePath, byte[] contents) =>
            File.WriteAllBytes(Path.Combine(repository.Path, relativePath), contents);

        internal void MakeExecutable(string relativePath)
        {
            if (OperatingSystem.IsWindows())
            {
                throw new PlatformNotSupportedException();
            }

            File.SetUnixFileMode(
                Path.Combine(repository.Path, relativePath),
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        internal void CommitTheoryChange()
        {
            Write("docs/develop/theory/volume/theory.md", "# changed\n");
            Commit("theory change");
        }

        internal void Commit(string message)
        {
            RunGit("add", "-A");
            RunGit("commit", "-qm", message);
        }

        internal ProcessOutput Propose() => RunScript(
            "propose",
            repository.Path,
            "HEAD^1",
            proposalPath);

        internal ProcessOutput Authorize(string proposal, string trusted) =>
            RunScript("authorize", proposal, trusted);

        internal ProcessOutput Validate(string baseRevision, string patch) =>
            RunScript("validate", repository.Path, baseRevision, patch);

        internal string CapturePatch(string revision, string pathspec = "Declared/Output")
        {
            var path = WriteExternal("captured.patch", string.Empty);
            var result = BoundedProcessRunner.Run(
                "git",
                ["diff", "--binary", "--full-index", "--no-renames", revision, "--", pathspec],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            File.WriteAllBytes(path, result.StandardOutput);
            return path;
        }

        internal string ReadProposal() => File.Exists(proposalPath)
            ? File.ReadAllText(proposalPath)
            : string.Empty;

        internal string ReadDotnetArguments() => File.Exists(dotnetArgumentsPath)
            ? File.ReadAllText(dotnetArgumentsPath)
            : string.Empty;

        internal string Read(string relativePath) =>
            File.ReadAllText(Path.Combine(repository.Path, relativePath));

        internal ProcessOutput WritebackBehindBaseAlreadyClosedCandidate()
        {
            Write("docs/develop/theory/volume/theory.md", "# candidate theory\n");
            Write("Declared/Output/generated.txt", "candidate closed output\n");
            Commit("closed candidate");
            var headSha = GitText("rev-parse", "HEAD");
            var forkSha = GitText("rev-parse", "HEAD^1");

            RunGit("switch", "--detach", forkSha);
            Write("Makefile", "# base-only producer change\n");
            Write("docs/develop/theory/base-only/theory.md", "# base-only theory\n");
            Commit("advance base");
            var baseSha = GitText("rev-parse", "HEAD");

            using var candidateData = new TemporaryDirectory();
            Directory.Delete(candidateData.Path);
            RunGit("clone", "-q", "--no-hardlinks", repository.Path, candidateData.Path);
            RunGitAt(candidateData.Path, "checkout", "--detach", headSha);

            Write("write-pattern.txt", "Declared/Output/**\n");
            Write("test-bin/dotnet", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$*" >> "$DOTNET_ARGUMENTS_PATH"
                cat "$WRITE_PATTERN_PATH"
                """ + "\n");
            Write("test-bin/make", """
                #!/usr/bin/env bash
                set -euo pipefail
                [[ "$1" == "-C" ]]
                printf '%s\n' 'candidate closed output' > "$2/Declared/Output/generated.txt"
                """ + "\n");
            MakeExecutable("test-bin/dotnet");
            MakeExecutable("test-bin/make");

            var proposal = CapturePatch(baseSha, headSha, ":(glob)Declared/Output/**");
            return RunScript(
                "writeback",
                repository.Path,
                candidateData.Path,
                proposal,
                baseSha,
                headSha,
                "candidate",
                repository.Path);
        }

        internal (ProcessOutput Output, string EventHeadSha, string ParentShas)
            WritebackWithDeclaredOutputDelta()
        {
            Write("docs/develop/theory/volume/theory.md", "# candidate theory\n");
            Commit("candidate theory change");
            var headSha = GitText("rev-parse", "HEAD");
            var forkSha = GitText("rev-parse", "HEAD^1");

            RunGit("switch", "--detach", forkSha);
            Write("docs/develop/theory/base-only/theory.md", "# base-only theory\n");
            Commit("advance base");
            var baseSha = GitText("rev-parse", "HEAD");

            using var candidateData = new TemporaryDirectory();
            Directory.Delete(candidateData.Path);
            RunGit("clone", "-q", "--no-hardlinks", repository.Path, candidateData.Path);
            RunGitAt(
                candidateData.Path,
                "fetch",
                "-q",
                "--no-tags",
                repository.Path,
                baseSha,
                headSha);
            RunGitAt(candidateData.Path, "checkout", "--detach", headSha);

            Write("write-pattern.txt", "Declared/Output/**\n");
            Write("test-bin/dotnet", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$*" >> "$DOTNET_ARGUMENTS_PATH"
                cat "$WRITE_PATTERN_PATH"
                """ + "\n");
            Write("test-bin/make", """
                #!/usr/bin/env bash
                set -euo pipefail
                [[ "$1" == "-C" ]]
                printf '%s\n' 'trusted recomputation' > "$2/Declared/Output/existing.txt"
                """ + "\n");
            MakeExecutable("test-bin/dotnet");
            MakeExecutable("test-bin/make");

            Write("Declared/Output/existing.txt", "trusted recomputation\n");
            var proposal = CapturePatch(baseSha, "Declared/Output");

            using var remote = new TemporaryDirectory();
            RunGitAt(remote.Path, "init", "--bare", "-q", ".");
            var output = RunScript(
                "writeback",
                repository.Path,
                candidateData.Path,
                proposal,
                baseSha,
                headSha,
                "candidate",
                remote.Path);
            var parentShas = output.ExitCode == 0
                ? GitTextAt(remote.Path, "show", "-s", "--format=%P", "refs/heads/candidate")
                : string.Empty;
            return (output, headSha, parentShas);
        }

        internal string WriteExternal(string name, string contents)
        {
            var path = Path.Combine(repository.Path, name);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
            return path;
        }

        private string CapturePatch(string oldRevision, string newRevision, string pathspec)
        {
            var path = WriteExternal("writeback-proposal.patch", string.Empty);
            var result = BoundedProcessRunner.Run(
                "git",
                [
                    "diff", "--binary", "--full-index", "--no-color", "--no-ext-diff",
                    "--no-renames", oldRevision, newRevision, "--", pathspec,
                ],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            File.WriteAllBytes(path, result.StandardOutput);
            return path;
        }

        private string GitText(params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, repository.Path, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        public void Dispose() => repository.Dispose();

        internal void RunGit(params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, repository.Path, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
        }

        private static void RunGitAt(string workingDirectory, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, workingDirectory, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
        }

        private static string GitTextAt(string workingDirectory, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, workingDirectory, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private ProcessOutput RunScript(params string[] arguments)
        {
            var script = Path.Combine(
                PrOpenScriptTests.RepositoryRoot(),
                "tools", "scripts", "workflow", "theory-ingest-closure.sh");
            return BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binDirectory}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"DOTNET_ARGUMENTS_PATH={dotnetArgumentsPath}",
                    $"WRITE_PATTERN_PATH={Path.Combine(repository.Path, "write-pattern.txt")}",
                    "bash",
                    script,
                    .. arguments,
                ],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }
    }
}
