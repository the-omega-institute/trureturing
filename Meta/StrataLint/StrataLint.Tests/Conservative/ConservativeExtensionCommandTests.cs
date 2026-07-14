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
        Assert.Equal(1, fixture.Environment.FreezeCount);
        Assert.Equal(2, fixture.Environment.Invocations.Count);
        Assert.Equal(
            [
                fixture.BaselineHarness,
                fixture.CandidateHarness,
                fixture.BaselineHarness,
                fixture.CandidateHarness,
                fixture.BaselineHarness,
                fixture.CandidateHarness,
            ],
            fixture.Environment.LoadedHarnessPaths);
        Assert.Single(
            fixture.Environment.Invocations.Select(static invocation => invocation.Replay.Root)
                .Distinct(StringComparer.Ordinal));
        Assert.All(
            fixture.Environment.Invocations,
            invocation => Assert.Equal(
                fixture.Environment.Corpus.Root,
                invocation.Replay.Corpus.Root));
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
    public void HarnessOutsideItsRepositoryIsInfrastructureFailure()
    {
        using var fixture = new CommandFixture();
        var arguments = fixture.Arguments.ToArray();
        arguments[Array.IndexOf(arguments, "--candidate-harness") + 1] = fixture.BaselineHarness;

        var result = ConservativeExtensionCommand.Run(arguments, fixture.Environment);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("candidate harness", result.Error, StringComparison.Ordinal);
        Assert.Contains("candidate root", result.Error, StringComparison.Ordinal);
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
    public void LeanReportMutationDuringReplayIsInfrastructureFailure()
    {
        using var fixture = new CommandFixture();
        fixture.Environment.MutateCandidateReportDuringFirstExecution = true;

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("report changed", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void RepositoryIdentityMutationDuringReplayIsInfrastructureFailure()
    {
        using var fixture = new CommandFixture();
        fixture.Environment.ChangeCandidateIdentityAfterFirstExecution = true;

        var result = ConservativeExtensionCommand.Run(fixture.Arguments, fixture.Environment);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("identity changed", result.Error, StringComparison.OrdinalIgnoreCase);
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
            BaselineHarness = Path.Combine(BaselineRoot, "baseline-harness.dll");
            CandidateHarness = Path.Combine(CandidateRoot, "candidate-harness.dll");
            File.WriteAllText(BaselineHarness, "baseline harness\n", new UTF8Encoding(false));
            File.WriteAllText(CandidateHarness, "candidate harness\n", new UTF8Encoding(false));
            Arguments =
            [
                "--baseline-root", BaselineRoot,
                "--candidate-root", CandidateRoot,
                "--baseline-lean-report", baselineReport,
                "--candidate-lean-report", candidateReport,
                "--baseline-harness", BaselineHarness,
                "--candidate-harness", CandidateHarness,
            ];
            Environment = new SyntheticCommandEnvironment(mutateCandidate);
        }

        internal string BaselineRoot { get; }

        internal string CandidateRoot { get; }

        internal string BaselineHarness { get; }

        internal string CandidateHarness { get; }

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
            var corpusBytes = Encoding.UTF8.GetBytes("{}\n").ToImmutableArray();
            Corpus = new MaterializedConservativeCorpus(
                corpusBytes,
                GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan()),
                [
                    ConservativeTestData.AdmitCase,
                    ConservativeTestData.RejectCase,
                    ConservativeTestData.Sl022RejectCase,
                ]);
        }

        internal MaterializedConservativeCorpus Corpus { get; }

        internal List<ConservativeHarnessInvocation> Invocations { get; } = [];

        internal List<string> LoadedHarnessPaths { get; } = [];

        internal int FreezeCount { get; private set; }

        internal Exception? MaterializationFailure { get; set; }

        internal Exception? ExecutionFailure { get; set; }

        internal bool MutateCandidateReportDuringFirstExecution { get; set; }

        internal bool ChangeCandidateIdentityAfterFirstExecution { get; set; }

        public MaterializedConservativeCorpus Materialize(string baselineRoot) =>
            MaterializationFailure is null ? Corpus : throw MaterializationFailure;

        public ConservativeRepositoryIdentity IdentifyRepository(string root)
        {
            if (root.EndsWith("baseline", StringComparison.Ordinal))
            {
                return new ConservativeRepositoryIdentity(input.BaselineCommitOid, input.BaselineTreeOid);
            }

            return ChangeCandidateIdentityAfterFirstExecution && Invocations.Count > 0
                ? new ConservativeRepositoryIdentity(input.CandidateCommitOid, new string('e', 40))
                : new ConservativeRepositoryIdentity(input.CandidateCommitOid, input.CandidateTreeOid);
        }

        public ConservativeHarnessProgram LoadHarness(string path)
        {
            LoadedHarnessPaths.Add(path);
            return path.EndsWith("baseline-harness.dll", StringComparison.Ordinal)
                ? new ConservativeHarnessProgram(path, input.BaselineHarnessRoot)
                : new ConservativeHarnessProgram(path, input.CandidateHarnessRoot);
        }

        public ConservativeReplayEnvelope Freeze(
            string baselineRoot,
            string candidateRoot,
            ConservativeRepositoryIdentity baselineIdentity,
            ConservativeRepositoryIdentity candidateIdentity,
            string baselineLeanReport,
            string candidateLeanReport,
            MaterializedConservativeCorpus corpus)
        {
            FreezeCount++;
            return ConservativeReplayEnvelopeCodec.Create(
                corpus,
                baselineIdentity,
                candidateIdentity,
                File.ReadAllBytes(baselineLeanReport),
                File.ReadAllBytes(candidateLeanReport),
                Encoding.UTF8.GetBytes("synthetic git bundle\n"));
        }

        public string FileRoot(string path) =>
            GoldenCorpusMaterializer.ContentRoot(File.ReadAllBytes(path));

        public ConservativeHarnessExecution Execute(ConservativeHarnessInvocation invocation)
        {
            Invocations.Add(invocation);
            if (ExecutionFailure is not null) throw ExecutionFailure;
            if (MutateCandidateReportDuringFirstExecution && Invocations.Count == 1)
            {
                File.AppendAllText(invocation.CandidateLeanReport, "changed\n", new UTF8Encoding(false));
            }

            return invocation.Program.Root == input.BaselineHarnessRoot
                ? input.BaselineExecution
                : input.CandidateExecution;
        }
    }
}
