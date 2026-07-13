using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeExtensionCommandTests
{
    [Fact]
    public void ConservativeSyntheticTreesReturnZeroAndCanonicalCertificate()
    {
        using var fixture = new CommandFixture();

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("CORPUS_CONSERVATIVE", result.Output, StringComparison.Ordinal);
        Assert.Empty(result.Error);
        Assert.Equal(2, fixture.Environment.Invocations.Count);
        Assert.All(
            fixture.Environment.Invocations,
            invocation => Assert.Equal(fixture.Environment.Corpus.Root, invocation.Corpus.Root));
    }

    [Fact]
    public void FlippedOldAdmitReturnsOne()
    {
        using var fixture = new CommandFixture(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.AdmitCase,
                ConservativeDisposition.Block,
                "SL-001"))
            .ToImmutableArray());

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("CONSERVATIVE_VIOLATION", result.Output, StringComparison.Ordinal);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void RemovedBlockWitnessReturnsOne()
    {
        using var fixture = new CommandFixture(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit))
            .ToImmutableArray());

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("CONSERVATIVE-BLOCK-WITNESS-LOST", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingCorpusIsInfrastructureFailure()
    {
        using var fixture = new CommandFixture();
        fixture.Environment.MaterializationFailure = new FileNotFoundException("base corpus missing");

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("base corpus missing", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void HarnessTimeoutIsInfrastructureFailure()
    {
        using var fixture = new CommandFixture();
        fixture.Environment.ExecutionFailure = new TimeoutException("candidate harness timed out");

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("timed out", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RepeatedCommandProducesIdenticalCertificateBytes()
    {
        using var firstFixture = new CommandFixture();
        using var secondFixture = new CommandFixture();

        var first = ConservativeExtensionCommand.Run(
            firstFixture.Arguments,
            firstFixture.Environment);
        var second = ConservativeExtensionCommand.Run(
            secondFixture.Arguments,
            secondFixture.Environment);

        Assert.Equal(0, first.ExitCode);
        Assert.Equal(0, second.ExitCode);
        Assert.Equal(first.Output, second.Output);
    }

    private sealed class CommandFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal CommandFixture(
            Func<ImmutableArray<ConservativeCaseResult>, ImmutableArray<ConservativeCaseResult>>?
                mutateCandidate = null)
        {
            BaselineRoot = Path.Combine(temporary.Path, "baseline");
            CandidateRoot = Path.Combine(temporary.Path, "candidate");
            Directory.CreateDirectory(BaselineRoot);
            Directory.CreateDirectory(CandidateRoot);
            var reports = Path.Combine(temporary.Path, "reports");
            Directory.CreateDirectory(reports);
            var baselineReport = Path.Combine(reports, "baseline.json");
            var candidateReport = Path.Combine(reports, "candidate.json");
            File.WriteAllText(baselineReport, "{}\n", new UTF8Encoding(false));
            File.WriteAllText(candidateReport, "{}\n", new UTF8Encoding(false));
            Arguments =
            [
                "--baseline-root", BaselineRoot,
                "--candidate-root", CandidateRoot,
                "--baseline-lean-report", baselineReport,
                "--candidate-lean-report", candidateReport,
            ];
            Environment = new SyntheticCommandEnvironment(mutateCandidate);
        }

        internal string BaselineRoot { get; }

        internal string CandidateRoot { get; }

        internal ImmutableArray<string> Arguments { get; }

        internal SyntheticCommandEnvironment Environment { get; }

        public void Dispose() => temporary.Dispose();
    }

    private sealed class SyntheticCommandEnvironment : IConservativeExtensionEnvironment
    {
        private readonly ConservativeVerificationInput input;

        internal SyntheticCommandEnvironment(
            Func<ImmutableArray<ConservativeCaseResult>, ImmutableArray<ConservativeCaseResult>>?
                mutateCandidate)
        {
            input = ConservativeTestData.Input(mutateCandidate);
            Corpus = new MaterializedConservativeCorpus(
                Encoding.UTF8.GetBytes("{}\n").ToImmutableArray(),
                input.CorpusRoot,
                [ConservativeTestData.AdmitCase, ConservativeTestData.RejectCase]);
        }

        internal MaterializedConservativeCorpus Corpus { get; }

        internal List<ConservativeHarnessInvocation> Invocations { get; } = [];

        internal Exception? MaterializationFailure { get; set; }

        internal Exception? ExecutionFailure { get; set; }

        public MaterializedConservativeCorpus Materialize(string baselineRoot) =>
            MaterializationFailure is null ? Corpus : throw MaterializationFailure;

        public ConservativeRepositoryIdentity IdentifyRepository(string root) =>
            root.EndsWith("baseline", StringComparison.Ordinal)
                ? new ConservativeRepositoryIdentity(input.BaselineCommitOid, input.BaselineTreeOid)
                : new ConservativeRepositoryIdentity(input.CandidateCommitOid, input.CandidateTreeOid);

        public ConservativeHarnessProgram LoadHarness(string root) =>
            root.EndsWith("baseline", StringComparison.Ordinal)
                ? new ConservativeHarnessProgram("baseline.dll", input.BaselineHarnessRoot)
                : new ConservativeHarnessProgram("candidate.dll", input.CandidateHarnessRoot);

        public string FileRoot(string path) =>
            path.EndsWith("baseline.json", StringComparison.Ordinal)
                ? input.BaselineLeanReportRoot
                : input.CandidateLeanReportRoot;

        public ConservativeHarnessExecution Execute(ConservativeHarnessInvocation invocation)
        {
            Invocations.Add(invocation);
            if (ExecutionFailure is not null) throw ExecutionFailure;
            return invocation.Program.Root == input.BaselineHarnessRoot
                ? input.BaselineExecution
                : input.CandidateExecution;
        }
    }
}
