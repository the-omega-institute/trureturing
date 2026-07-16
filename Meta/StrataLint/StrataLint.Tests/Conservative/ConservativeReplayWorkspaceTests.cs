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

    private static string GitText(string root, params string[] arguments) =>
        Encoding.UTF8.GetString(Git(root, (IEnumerable<string>)arguments).StandardOutput).Trim();

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
