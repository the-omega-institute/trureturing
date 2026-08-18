using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryIngestClosureScriptTests
{
    [Theory]
    [InlineData("D5/Test.lean")]
    [InlineData("Trureturing.lean")]
    [InlineData("lean-toolchain")]
    [InlineData("lake-manifest.json")]
    [InlineData("lakefile.toml")]
    [InlineData("lakefile.lean")]
    [InlineData("Makefile")]
    [InlineData("tools/StrataLint.Engine/Test.cs")]
    [InlineData("tools/scripts/ingest.sh")]
    [InlineData("Meta/FILEMAP.toml")]
    [InlineData(".github/workflows/theory-ingest.yml")]
    public void EventHeadLeanReportInputClosureChangesFailClosed(string path)
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.ChangeCandidate(path, "candidate-controlled change\n");

        var result = fixture.GuardInputs();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "split the theory-only PR",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateTheorySymlinkFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TheoryIngestClosureFixture();
        fixture.AddCandidateTheorySymlink();

        var result = fixture.GuardInputs();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "candidate theory source is not a regular file",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidDeletePatchIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.DeleteBase("Declared/Output/existing.txt");
        var patch = fixture.CaptureBasePatch("Declared/Output");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("THEORY-INGEST-CLOSURE-001", Error(result), StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidModeChangePatchIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TheoryIngestClosureFixture();
        fixture.MakeBaseExecutable("Declared/Output/existing.txt");
        var patch = fixture.CaptureBasePatch("Declared/Output");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("symlink/submodule", Error(result), StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidBinaryPatchIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.WriteBaseBytes("Declared/Output/existing.txt", [0, 1, 2, 3]);
        var patch = fixture.CaptureBasePatch("Declared/Output");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("binary patches are not authorized", Error(result), StringComparison.Ordinal);
    }

    [Fact]
    public void StructurallyInvalidPathOutsideFileMapWriteSetIsRejected()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.WriteBase("Outside/existing.txt", "changed outside\n");
        var patch = fixture.CaptureBasePatch("Outside");

        var result = fixture.Validate("HEAD", patch);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("outside the FILEMAP-derived write set", Error(result), StringComparison.Ordinal);
    }

    [Fact]
    public void TrustedPreparationProducesCanonicalBoundEnvelopeAndSelfVerifiedPatch()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.ChangeCandidateTheory();

        var result = fixture.PrepareFromOutsideRepository();

        Assert.True(result.ExitCode == 0, Diagnostic("prepare", result));
        Assert.True(fixture.ArtifactPatchExists());
        Assert.True(fixture.ArtifactEnvelopeExists());
        Assert.True(fixture.ArtifactEnvelopeDigestExists());
        using var envelope = JsonDocument.Parse(fixture.ReadArtifactEnvelope());
        Assert.Equal(
            new[]
            {
                "base_sha",
                "head_sha",
                "patch_sha256",
                "report_input_address",
                "report_sha256",
                "theory_tree_sha",
            },
            envelope.RootElement.EnumerateObject().Select(static property => property.Name).ToArray());
        Assert.Equal(fixture.BaseSha, envelope.RootElement.GetProperty("base_sha").GetString());
        Assert.Equal(fixture.HeadSha, envelope.RootElement.GetProperty("head_sha").GetString());
        Assert.Equal("sha256:" + new string('a', 64), envelope.RootElement
            .GetProperty("report_input_address").GetString());
        Assert.Contains("Declared/Output/existing.txt", fixture.ReadArtifactPatch());
        Assert.Contains(
            "filemap-conform --producer-write-set IngestCommand",
            fixture.ReadDotnetArguments(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackCommitHasExactlyEventHeadAsItsParent()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.ChangeCandidateTheory();
        var prepare = fixture.Prepare();
        Assert.True(prepare.ExitCode == 0, Diagnostic("prepare", prepare));
        fixture.SeedRemoteAtEventHead();

        var result = fixture.Writeback();

        Assert.True(result.ExitCode == 0, Diagnostic("writeback", result));
        Assert.Equal(fixture.HeadSha, fixture.RemoteCommitParents());
    }

    [Fact]
    public void WritebackRejectsEnvelopeWhoseDigestDoesNotMatch()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.ChangeCandidateTheory();
        var prepare = fixture.Prepare();
        Assert.True(prepare.ExitCode == 0, Diagnostic("prepare", prepare));
        fixture.SeedRemoteAtEventHead();
        File.AppendAllText(fixture.ArtifactEnvelope, " \n", new UTF8Encoding(false));

        var result = fixture.Writeback();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("envelope digest", Error(result), StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackRejectsRemoteHeadDrift()
    {
        using var fixture = new TheoryIngestClosureFixture();
        fixture.ChangeCandidateTheory();
        var prepare = fixture.Prepare();
        Assert.True(prepare.ExitCode == 0, Diagnostic("prepare", prepare));
        fixture.SeedRemoteAtEventHead();
        fixture.AdvanceRemoteHead();

        var result = fixture.Writeback();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("remote head drifted from the event head", Error(result), StringComparison.Ordinal);
    }

    private static string Error(ProcessOutput output) => Encoding.UTF8.GetString(output.StandardError);

    private static string Diagnostic(string operation, ProcessOutput output) =>
        $"{operation} exited {output.ExitCode}\n"
        + $"stdout:\n{Encoding.UTF8.GetString(output.StandardOutput)}\n"
        + $"stderr:\n{Encoding.UTF8.GetString(output.StandardError)}";

    private sealed class TheoryIngestClosureFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();
        private readonly TemporaryDirectory candidate = new();
        private readonly TemporaryDirectory artifact = new();
        private readonly TemporaryDirectory remote = new();
        private readonly TemporaryDirectory validator = new();
        private readonly string binDirectory;
        private readonly string dotnetArgumentsPath;
        private bool candidateChanged;

        internal TheoryIngestClosureFixture()
        {
            Directory.Delete(candidate.Path);
            Directory.Delete(validator.Path);
            RunGitAt(repository.Path, "init", "-q");
            Configure(repository.Path);
            WriteBase("Declared/Output/existing.txt", "base output\n");
            WriteBase("Outside/existing.txt", "base outside\n");
            WriteBase("docs/develop/theory/volume/theory.md", "# volume\n");
            WriteBase("D5/Test.lean", "def test : Nat := 1\n");
            WriteBase("Trureturing.lean", "import D5.Test\n");
            WriteBase("lean-toolchain", "leanprover/lean4:v4.0.0\n");
            WriteBase("lake-manifest.json", "{}\n");
            WriteBase("lakefile.toml", "name = \"fixture\"\n");
            WriteBase("lakefile.lean", "import Lake\n");
            WriteBase("Makefile", "# fixture\n");
            WriteBase("tools/StrataLint.Engine/Test.cs", "// fixture\n");
            WriteBase("tools/scripts/ingest.sh", "#!/usr/bin/env bash\n");
            WriteBase(".github/workflows/theory-ingest.yml", "name: fixture\n");
            WriteBase("Meta/FILEMAP.toml", FileMap);
            WriteBase("tools/scripts/report/lean-report-input.sh", ReportInputHelper);
            MakeExecutable(repository.Path, "tools/scripts/report/lean-report-input.sh");
            RunGitAt(repository.Path, "add", "-A");
            RunGitAt(repository.Path, "commit", "-qm", "base");
            BaseSha = GitTextAt(repository.Path, "rev-parse", "HEAD");

            RunGitAt(
                repository.Path,
                "clone",
                "-q",
                "--no-hardlinks",
                repository.Path,
                candidate.Path);
            Configure(candidate.Path);
            RunGitAt(
                repository.Path,
                "clone",
                "-q",
                "--no-hardlinks",
                repository.Path,
                validator.Path);

            binDirectory = Path.Combine(repository.Path, "test-bin");
            dotnetArgumentsPath = Path.Combine(repository.Path, "dotnet-arguments.txt");
            Directory.CreateDirectory(binDirectory);
            WriteAbsolute(Path.Combine(binDirectory, "dotnet"), DotnetStub);
            WriteAbsolute(Path.Combine(binDirectory, "make"), MakeStub);
            MakeExecutable(repository.Path, "test-bin/dotnet");
            MakeExecutable(repository.Path, "test-bin/make");
            InstallReport(repository.Path);

            RunGitAt(remote.Path, "init", "--bare", "-q", ".");
        }

        internal string BaseSha { get; }

        internal string HeadSha => GitTextAt(candidate.Path, "rev-parse", "HEAD");

        internal string ArtifactPatch => Path.Combine(artifact.Path, "theory-ingest.patch");

        internal string ArtifactEnvelope => Path.Combine(artifact.Path, "theory-ingest-envelope.json");

        internal string ArtifactEnvelopeDigest => ArtifactEnvelope + ".sha256";

        internal bool ArtifactPatchExists() => File.Exists(ArtifactPatch);

        internal bool ArtifactEnvelopeExists() => File.Exists(ArtifactEnvelope);

        internal bool ArtifactEnvelopeDigestExists() => File.Exists(ArtifactEnvelopeDigest);

        internal byte[] ReadArtifactEnvelope() => File.ReadAllBytes(ArtifactEnvelope);

        internal string ReadArtifactPatch() => File.ReadAllText(ArtifactPatch);

        internal void ChangeCandidateTheory() =>
            ChangeCandidate("docs/develop/theory/volume/theory.md", "# candidate theory\n");

        internal void ChangeCandidate(string path, string contents)
        {
            WriteAt(candidate.Path, path, contents);
            CommitCandidate("candidate change");
        }

        internal void AddCandidateTheorySymlink()
        {
            var link = Path.Combine(candidate.Path, "docs", "develop", "theory", "linked.md");
            File.CreateSymbolicLink(link, "volume/theory.md");
            CommitCandidate("candidate symlink");
        }

        internal ProcessOutput GuardInputs()
        {
            EnsureCandidateChanged();
            return RunScript(
                repository.Path,
                "guard-inputs",
                repository.Path,
                candidate.Path,
                BaseSha,
                HeadSha);
        }

        internal ProcessOutput Prepare()
        {
            EnsureCandidateChanged();
            return RunScript(
                repository.Path,
                "prepare",
                repository.Path,
                candidate.Path,
                BaseSha,
                HeadSha,
                artifact.Path);
        }

        internal ProcessOutput PrepareFromOutsideRepository()
        {
            EnsureCandidateChanged();
            using var outside = new TemporaryDirectory();
            return RunScript(
                outside.Path,
                "prepare",
                repository.Path,
                candidate.Path,
                BaseSha,
                HeadSha,
                artifact.Path);
        }

        internal void SeedRemoteAtEventHead() => RunGitAt(
            candidate.Path,
            "push",
            "-q",
            remote.Path,
            $"{HeadSha}:refs/heads/candidate");

        internal void AdvanceRemoteHead()
        {
            WriteAt(candidate.Path, "docs/develop/theory/volume/after.md", "# after\n");
            CommitCandidate("advance remote");
            RunGitAt(candidate.Path, "push", "-q", remote.Path, "HEAD:refs/heads/candidate");
        }

        internal ProcessOutput Writeback() => RunScript(
            validator.Path,
            "writeback",
            validator.Path,
            artifact.Path,
            BaseSha,
            JsonDocument.Parse(File.ReadAllBytes(ArtifactEnvelope)).RootElement
                .GetProperty("head_sha").GetString()!,
            "candidate",
            remote.Path);

        internal string RemoteCommitParents() => GitTextAt(
            remote.Path,
            "show",
            "-s",
            "--format=%P",
            "refs/heads/candidate");

        internal ProcessOutput Validate(string revision, string patch) => RunScript(
            repository.Path,
            "validate",
            repository.Path,
            revision,
            patch);

        internal void WriteBase(string path, string contents) => WriteAt(repository.Path, path, contents);

        internal void WriteBaseBytes(string path, byte[] bytes)
        {
            var fullPath = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllBytes(fullPath, bytes);
        }

        internal void DeleteBase(string path) => File.Delete(Path.Combine(repository.Path, path));

        internal void MakeBaseExecutable(string path) => MakeExecutable(repository.Path, path);

        internal string CaptureBasePatch(string pathspec)
        {
            var path = Path.Combine(repository.Path, "captured.patch");
            var result = BoundedProcessRunner.Run(
                "git",
                ["diff", "--binary", "--full-index", "--no-renames", "HEAD", "--", pathspec],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            File.WriteAllBytes(path, result.StandardOutput);
            return path;
        }

        internal string ReadDotnetArguments() => File.Exists(dotnetArgumentsPath)
            ? File.ReadAllText(dotnetArgumentsPath)
            : string.Empty;

        public void Dispose()
        {
            repository.Dispose();
            candidate.Dispose();
            artifact.Dispose();
            remote.Dispose();
            validator.Dispose();
        }

        private void EnsureCandidateChanged()
        {
            if (!candidateChanged)
            {
                ChangeCandidateTheory();
            }
        }

        private void CommitCandidate(string message)
        {
            RunGitAt(candidate.Path, "add", "-A");
            RunGitAt(candidate.Path, "commit", "-qm", message);
            candidateChanged = true;
        }

        private ProcessOutput RunScript(string workingDirectory, params string[] arguments)
        {
            var script = Path.Combine(
                PrOpenScriptTests.RepositoryRoot(),
                "tools",
                "scripts",
                "workflow",
                "theory-ingest-closure.sh");
            return BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binDirectory}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"DOTNET_ARGUMENTS_PATH={dotnetArgumentsPath}",
                    "bash",
                    script,
                    .. arguments,
                ],
                workingDirectory,
                TimeSpan.FromSeconds(60),
                1024 * 1024);
        }

        private static void InstallReport(string root)
        {
            var report = Path.Combine(root, ".lake", "build", "stratalint", "raw-lean-report.json");
            Directory.CreateDirectory(Path.GetDirectoryName(report)!);
            File.WriteAllText(report, "{}\n", new UTF8Encoding(false));
            var sha = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
                File.ReadAllBytes(report)));
            File.WriteAllText(report + ".sha256", $"{sha}  raw-lean-report.json\n");
            File.WriteAllText(report + ".input.attestation", "fixture\n");
            File.WriteAllText(report + ".provenance.json", "{}\n");
        }

        private static void Configure(string root)
        {
            RunGitAt(root, "config", "user.email", "test@example.com");
            RunGitAt(root, "config", "user.name", "test");
        }

        private static void WriteAt(string root, string path, string contents)
        {
            var fullPath = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, contents, new UTF8Encoding(false));
        }

        private static void WriteAbsolute(string path, string contents) =>
            File.WriteAllText(path, contents, new UTF8Encoding(false));

        private static void MakeExecutable(string root, string path)
        {
            if (OperatingSystem.IsWindows()) return;
            File.SetUnixFileMode(
                Path.Combine(root, path),
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        private static void RunGitAt(string root, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, root, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostic("git " + string.Join(' ', arguments), result));
        }

        private static string GitTextAt(string root, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git", arguments, root, TimeSpan.FromSeconds(30), 1024 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostic("git " + string.Join(' ', arguments), result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private const string FileMap = """
            schema_version = 2

            [residence_policy]
            case_id = "fixture"
            desired = "fixture"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Declared/Output/**"
            kind = "ledger"
            produced_by = "IngestCommand"
            consumed_by = ["fixture"]
            verified_by = ["fixture"]
            artifact_id = "none"
            runtime_disposition = "committed-ledger"
            """ + "\n";

        private static readonly string ReportInputHelper = """
            #!/usr/bin/env bash
            set -euo pipefail
            case "$1" in
              address)
                printf '%s %s %s %s\n' \
                  'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' \
                  'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' \
                  'cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc' \
                  'dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd'
                ;;
              verify) exit 0 ;;
              *) exit 2 ;;
            esac
            """ + "\n";

        private static readonly string DotnetStub = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$*" >> "$DOTNET_ARGUMENTS_PATH"
            [[ -f Meta/FILEMAP.toml ]]
            printf '%s\n' 'Declared/Output/**'
            """ + "\n";

        private static readonly string MakeStub = """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "$1" == "-C" ]]
            repository="$2"
            shift 2
            [[ "$1" == "ingest" ]]
            printf '%s\n' 'trusted recomputation' > "$repository/Declared/Output/existing.txt"
            """ + "\n";
    }
}
