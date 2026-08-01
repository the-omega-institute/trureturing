using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ConservativeReplayWorkspaceTests
{
    [Fact]
    public void BaselineScribeMismatchIsSoftOnlyForProtectedReplay()
    {
        var report = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var verifier = new FailingScribeEmissionVerifier();

        var protectedResult = ConservativeActualTreeEvaluator.VerifyBaselineScribeForReplay(
            verifier,
            report,
            RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]));

        Assert.Null(protectedResult);
        Assert.Throws<InvalidOperationException>(() =>
            ConservativeActualTreeEvaluator.VerifyBaselineScribeForReplay(
                verifier,
                report,
                RawChangeSet.Create([RuleFixture.BlueprintPath])));
    }

    [Fact]
    public void ValuesKernelReplayPathRequiresAUniqueByteExactRelocation()
    {
        const string historicalPath = "Archive/values-kernels.toml";
        const string bytes = "[[kernels]]\nname = \"fixture\"\n";
        var candidate = Snapshot((ValuesProjectionLoader.KernelDataPath, bytes));

        Assert.Equal(
            ValuesProjectionLoader.KernelDataPath,
            ConservativeActualTreeEvaluator.ResolveValuesKernelDataPathForReplay(
                candidate,
                candidate));
        Assert.Equal(
            historicalPath,
            ConservativeActualTreeEvaluator.ResolveValuesKernelDataPathForReplay(
                Snapshot((historicalPath, bytes)),
                candidate));
        Assert.Throws<InvalidOperationException>(() =>
            ConservativeActualTreeEvaluator.ResolveValuesKernelDataPathForReplay(
                Snapshot((historicalPath, "changed\n")),
                candidate));
        Assert.Throws<InvalidOperationException>(() =>
            ConservativeActualTreeEvaluator.ResolveValuesKernelDataPathForReplay(
                Snapshot(
                    (historicalPath, bytes),
                    ("Second/values-kernels.toml", bytes)),
                candidate));
    }

    [Fact]
    public void WorkerProtocolExposesNoRepositoryOrReportPathArguments()
    {
        var source = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(),
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "Conservative",
            "ConservativeCorpusWorker.cs"));

        Assert.DoesNotContain("--baseline-root", source, StringComparison.Ordinal);
        Assert.DoesNotContain("--candidate-root", source, StringComparison.Ordinal);
        Assert.DoesNotContain("--baseline-lean-report", source, StringComparison.Ordinal);
        Assert.DoesNotContain("--candidate-lean-report", source, StringComparison.Ordinal);
        Assert.DoesNotContain("--corpus", source, StringComparison.Ordinal);
        Assert.Contains("OpenStandardInput", source, StringComparison.Ordinal);

        var actualEvaluator = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(),
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "Conservative",
            "ConservativeActualTreeEvaluator.cs"));
        Assert.DoesNotContain("File.ReadAllBytes", actualEvaluator, StringComparison.Ordinal);
        Assert.Contains("ReadRevisionFile", actualEvaluator, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "candidateRepository.ReadRevision(",
            actualEvaluator,
            StringComparison.Ordinal);

        var corpusEvaluator = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(),
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "Conservative",
            "ConservativeCorpusEvaluator.cs"));
        var productionCheck = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(),
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "Admission",
            "ProductionCliEnvironment.cs"));
        Assert.Contains("SnapshotAdmissionCore.Evaluate", corpusEvaluator, StringComparison.Ordinal);
        Assert.DoesNotContain("RuleCatalog.Default.Execute", corpusEvaluator, StringComparison.Ordinal);
        Assert.Contains("SnapshotAdmissionCore.Evaluate", productionCheck, StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionFileReadRequiresOneExactCommitAndCommittedBlob()
    {
        using var repository = new TemporaryDirectory();
        Git(repository.Path, "init", "-b", "dev");
        Git(repository.Path, "config", "user.name", "StrataLint Fixture");
        Git(repository.Path, "config", "user.email", "fixture@example.invalid");
        var golden = Path.Combine(repository.Path, "Golden");
        Directory.CreateDirectory(golden);
        File.WriteAllText(
            Path.Combine(golden, "values-kernels.toml"),
            "kernel data\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "unrelated.txt"),
            "unrelated\n",
            new UTF8Encoding(false));
        Git(repository.Path, "add", ".");
        Git(repository.Path, "commit", "-m", "candidate");
        var gateway = new GitRepositoryGateway(repository.Path);
        var candidate = gateway.ResolveCurrentRevision();
        var tree = GitText(repository.Path, "rev-parse", "HEAD^{tree}");
        var blob = GitText(
            repository.Path,
            "rev-parse",
            $"HEAD:{ValuesProjectionLoader.KernelDataPath}");
        Git(repository.Path, "tag", "-a", "candidate-tag", "-m", "candidate tag");
        var tag = GitText(repository.Path, "rev-parse", "candidate-tag^{tag}");

        var entry = gateway.ReadRevisionFile(
            candidate.Revision,
            ValuesProjectionLoader.KernelDataPath);

        Assert.Equal(ValuesProjectionLoader.KernelDataPath, entry.Path);
        Assert.Equal("kernel data\n", Encoding.UTF8.GetString(entry.Bytes.AsSpan()));
        Assert.All(
            new[] { tree, blob, tag },
            nonCommit => Assert.Throws<InvalidOperationException>(() =>
                gateway.ReadRevisionFile(nonCommit, ValuesProjectionLoader.KernelDataPath)));
        Assert.Throws<InvalidOperationException>(() =>
            gateway.ReadRevisionFile(candidate.Revision, "Golden/missing.toml"));
    }

    [Fact]
    public void EnvelopeBytesRestoreTwoExactDetachedCheckouts()
    {
        using var repository = new TemporaryDirectory();
        Git(repository.Path, "init", "-b", "dev");
        Git(repository.Path, "config", "user.name", "StrataLint Fixture");
        Git(repository.Path, "config", "user.email", "fixture@example.invalid");
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "baseline\n", new UTF8Encoding(false));
        Git(repository.Path, "add", "tracked.txt");
        Git(repository.Path, "commit", "-m", "baseline");
        var baseline = new GitRepositoryGateway(repository.Path).ResolveCurrentRevision();
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "candidate\n", new UTF8Encoding(false));
        Git(repository.Path, "commit", "-am", "candidate");
        var candidate = new GitRepositoryGateway(repository.Path).ResolveCurrentRevision();
        var bundlePath = Path.Combine(repository.Path, "repository.bundle");
        Git(repository.Path, "bundle", "create", bundlePath, "HEAD");
        var corpusBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{}\n"));
        var envelope = ConservativeReplayEnvelopeCodec.Create(
            new MaterializedConservativeCorpus(
                corpusBytes,
                GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan()),
                ["golden:fixture"]),
            new ConservativeRepositoryIdentity(baseline.Revision, baseline.TreeOid),
            new ConservativeRepositoryIdentity(candidate.Revision, candidate.TreeOid),
            Encoding.UTF8.GetBytes("baseline-report\n"),
            Encoding.UTF8.GetBytes("candidate-report\n"),
            File.ReadAllBytes(bundlePath));

        using var workspace = ConservativeReplayWorkspace.Materialize(envelope);

        Assert.Equal(baseline.Revision, GitText(workspace.BaselineRoot, "rev-parse", "HEAD"));
        Assert.Equal(candidate.Revision, GitText(workspace.CandidateRoot, "rev-parse", "HEAD"));
        Assert.Equal("baseline\n", File.ReadAllText(Path.Combine(workspace.BaselineRoot, "tracked.txt")));
        Assert.Equal("candidate\n", File.ReadAllText(Path.Combine(workspace.CandidateRoot, "tracked.txt")));
        Assert.Equal("baseline-report\n", File.ReadAllText(workspace.BaselineLeanReport));
        Assert.Equal("candidate-report\n", File.ReadAllText(workspace.CandidateLeanReport));
    }

    [Fact]
    public void RepositoryBundleIncludesExactEvidenceCommitClosureFromBaseline()
    {
        using var baseline = new TemporaryDirectory();
        Git(baseline.Path, "init", "-b", "dev");
        Git(baseline.Path, "config", "user.name", "StrataLint Fixture");
        Git(baseline.Path, "config", "user.email", "fixture@example.invalid");
        File.WriteAllText(
            Path.Combine(baseline.Path, "evidence.txt"),
            "baseline-only evidence\n",
            new UTF8Encoding(false));
        Git(baseline.Path, "add", "evidence.txt");
        Git(baseline.Path, "commit", "-m", "baseline-only evidence");
        var evidenceCommit = GitText(baseline.Path, "rev-parse", "HEAD");
        var evidenceTree = GitText(baseline.Path, "rev-parse", "HEAD^{tree}");
        var evidenceBlob = GitText(baseline.Path, "rev-parse", "HEAD:evidence.txt");

        using var candidate = new TemporaryDirectory();
        Git(candidate.Path, "init", "-b", "dev");
        Git(candidate.Path, "config", "user.name", "StrataLint Fixture");
        Git(candidate.Path, "config", "user.email", "fixture@example.invalid");
        File.WriteAllText(Path.Combine(candidate.Path, "tracked.txt"), "baseline\n", new UTF8Encoding(false));
        Git(candidate.Path, "add", "tracked.txt");
        Git(candidate.Path, "commit", "-m", "candidate baseline");
        var baselineIdentity = new GitRepositoryGateway(candidate.Path).ResolveCurrentRevision();
        File.WriteAllText(Path.Combine(candidate.Path, "tracked.txt"), "candidate\n", new UTF8Encoding(false));
        Git(candidate.Path, "commit", "-am", "candidate head");
        var candidateIdentity = new GitRepositoryGateway(candidate.Path).ResolveCurrentRevision();

        var bundle = ConservativeRepositoryBundle.Create(
            baseline.Path,
            candidate.Path,
            new ConservativeRepositoryIdentity(baselineIdentity.Revision, baselineIdentity.TreeOid),
            new ConservativeRepositoryIdentity(candidateIdentity.Revision, candidateIdentity.TreeOid),
            [evidenceCommit]);
        var corpusBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{}\n"));
        var envelope = ConservativeReplayEnvelopeCodec.Create(
            new MaterializedConservativeCorpus(
                corpusBytes,
                GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan()),
                ["golden:fixture"]),
            new ConservativeRepositoryIdentity(baselineIdentity.Revision, baselineIdentity.TreeOid),
            new ConservativeRepositoryIdentity(candidateIdentity.Revision, candidateIdentity.TreeOid),
            Encoding.UTF8.GetBytes("baseline-report\n"),
            Encoding.UTF8.GetBytes("candidate-report\n"),
            bundle);

        using var workspace = ConservativeReplayWorkspace.Materialize(envelope);

        foreach (var root in new[] { workspace.BaselineRoot, workspace.CandidateRoot })
        {
            Assert.Equal("commit", GitText(root, "cat-file", "-t", evidenceCommit));
            Assert.Equal("tree", GitText(root, "cat-file", "-t", evidenceTree));
            Assert.Equal("blob", GitText(root, "cat-file", "-t", evidenceBlob));
        }
    }

    [Fact]
    public void RepositoryBundlePreservesSha256ObjectFormat()
    {
        using var repository = new TemporaryDirectory();
        Git(repository.Path, "init", "--object-format=sha256", "-b", "dev");
        Git(repository.Path, "config", "user.name", "StrataLint Fixture");
        Git(repository.Path, "config", "user.email", "fixture@example.invalid");
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "baseline\n", new UTF8Encoding(false));
        Git(repository.Path, "add", "tracked.txt");
        Git(repository.Path, "commit", "-m", "baseline");
        var baseline = new GitRepositoryGateway(repository.Path).ResolveCurrentRevision();
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "candidate\n", new UTF8Encoding(false));
        Git(repository.Path, "commit", "-am", "candidate");
        var candidate = new GitRepositoryGateway(repository.Path).ResolveCurrentRevision();

        var bundle = ConservativeRepositoryBundle.Create(
            repository.Path,
            repository.Path,
            new ConservativeRepositoryIdentity(baseline.Revision, baseline.TreeOid),
            new ConservativeRepositoryIdentity(candidate.Revision, candidate.TreeOid),
            Array.Empty<string>());
        var corpusBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{}\n"));
        var envelope = ConservativeReplayEnvelopeCodec.Create(
            new MaterializedConservativeCorpus(
                corpusBytes,
                GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan()),
                ["golden:fixture"]),
            new ConservativeRepositoryIdentity(baseline.Revision, baseline.TreeOid),
            new ConservativeRepositoryIdentity(candidate.Revision, candidate.TreeOid),
            Encoding.UTF8.GetBytes("baseline-report\n"),
            Encoding.UTF8.GetBytes("candidate-report\n"),
            bundle);

        using var workspace = ConservativeReplayWorkspace.Materialize(envelope);

        Assert.Equal("sha256", GitText(workspace.BaselineRoot, "rev-parse", "--show-object-format"));
        Assert.Equal("sha256", GitText(workspace.CandidateRoot, "rev-parse", "--show-object-format"));
        Assert.Equal(baseline.Revision, GitText(workspace.BaselineRoot, "rev-parse", "HEAD"));
        Assert.Equal(candidate.Revision, GitText(workspace.CandidateRoot, "rev-parse", "HEAD"));
    }

    [Fact]
    public void RepositoryBundleRejectsMixedObjectFormatsBeforeImport()
    {
        using var sha1 = CreateRepository("sha1", "sha1");
        using var sha256 = CreateRepository("sha256", "sha256");
        var baseline = new GitRepositoryGateway(sha1.Path).ResolveCurrentRevision();
        var candidate = new GitRepositoryGateway(sha256.Path).ResolveCurrentRevision();

        var exception = Assert.Throws<InvalidOperationException>(() =>
            ConservativeRepositoryBundle.Create(
                sha1.Path,
                sha256.Path,
                new ConservativeRepositoryIdentity(baseline.Revision, baseline.TreeOid),
                new ConservativeRepositoryIdentity(candidate.Revision, candidate.TreeOid),
                Array.Empty<string>()));

        Assert.Equal("conservative bundle cannot mix Git object formats", exception.Message);
    }

    private static string GitText(string root, params string[] arguments) =>
        Encoding.UTF8.GetString(Git(root, (IEnumerable<string>)arguments).StandardOutput).Trim();

    private static TemporaryDirectory CreateRepository(string objectFormat, string text)
    {
        return TemporaryDirectory.Create(repositoryPath =>
        {
            Git(repositoryPath, "init", $"--object-format={objectFormat}", "-b", "dev");
            Git(repositoryPath, "config", "user.name", "StrataLint Fixture");
            Git(repositoryPath, "config", "user.email", "fixture@example.invalid");
            File.WriteAllText(Path.Combine(repositoryPath, "tracked.txt"), text + "\n", new UTF8Encoding(false));
            Git(repositoryPath, "add", "tracked.txt");
            Git(repositoryPath, "commit", "-m", text);
        });
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(file =>
                RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;

    private static void Git(string root, params string[] arguments)
    {
        var result = Git(root, (IEnumerable<string>)arguments);
        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
    }

    private static ProcessOutput Git(string root, IEnumerable<string> arguments) =>
        BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromSeconds(30),
            4 * 1024 * 1024);

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private sealed class FailingScribeEmissionVerifier : IScribeEmissionVerifier
    {
        public VerifiedScribeEmissions Verify(LeanAxiomReport report) =>
            throw new InvalidOperationException("synthetic Scribe mismatch");
    }
}
