using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Tests;

public sealed partial class CoverBatchCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CompleteProducerPipelineSharesInputsAndPreservesLedgerBytes(bool partialFailure)
    {
        using var sequential = new BatchWorld();
        WriteProblem(sequential.Root);
        sequential.RunSingles(new ProductionScribeEmissionVerifier(typeof(BatchClaimDefinition).Assembly));
        using var batch = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(batch.Root);
        var reportPath = batch.WriteReportBundle();
        foreach (var path in new[] { "Blueprint/D5/S0/Carrier/Probe.md", CanonicalValuesWriter.RelativePath })
        {
            ReviewRegressionTests.RunGit(batch.Root, "ls-files", "--error-unmatch", path);
            TemporaryFileSystem.File.Delete(Path.Combine(batch.Root, path));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(batch.Root, path)));
        }
        var input = Row(First, Gid) + (partialFailure ? Row("missing-atom", Gid) : "") + Row(Second, OtherGid);
        FrozenLoadCounter frozen;
        LedgerLoadCounter ledger;
        ReportLoadCounter reports;
        CommandResult result;
        var discoveries = 0;
        BatchClaimDefinition.Creating.Value = () => discoveries++;
        try
        {
            using (frozen = new FrozenLoadCounter())
            using (ledger = new LedgerLoadCounter())
            using (reports = new ReportLoadCounter())
                result = batch.RunProducers(input);
        }
        finally
        {
            BatchClaimDefinition.Creating.Value = null;
        }

        output.WriteLine(result.Output + result.Error);
        Assert.Equal(4, discoveries);
        Assert.Equal(partialFailure ? 1 : 0, result.ExitCode);
        Assert.Equal(partialFailure ? ["applied", "failed", "applied"] : ["applied", "applied"],
            Results(result).Select(item => item.Status).ToArray());
        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
        Assert.Empty(result.Error);
        foreach (var path in new[] { "Blueprint/D5/S0/Carrier/Probe.md", CanonicalValuesWriter.RelativePath,
                     "tools/Generated/scribe-emissions.v1.json", "Generated/FILEMAP.md", "Generated/DAG.md",
                     "Generated/truth-graph.v1.json" })
        {
            Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(batch.Root, path)));
            Assert.Single(result.Output.Split('\n'), line => line.Contains(path, StringComparison.Ordinal));
        }
        Assert.Equal(1, reports.Loads);
        Assert.Equal(1, frozen.Catalogs);
        Assert.Equal(1, frozen.Indexes);
        Assert.Equal(1, ledger.BaselineLoads);
        Assert.Equal([1, 1, 1], ledger.CandidateSnapshotLoads);
        output.WriteLine("COMPLETE_PRODUCERS synthetic_assembly=true report={0} catalog={1} index={2} baseline={3} candidate=[{4}] discoveries={5}",
            reports.Loads, frozen.Catalogs, frozen.Indexes, ledger.BaselineLoads,
            string.Join(',', ledger.CandidateSnapshotLoads), discoveries);
        Assert.True(TemporaryFileSystem.File.Exists(reportPath));

        var graphPath = Path.Combine(batch.Root, "Generated/truth-graph.v1.json");
        var emittedGraph = TemporaryFileSystem.File.ReadAllBytes(graphPath);
        var truth = DagLedgerCommandPreparation.BuildTruth(batch.Repository, new PrecomputedLeanReportSource(batch.Root));
        var check = DagRenderCommand.Run(batch.Root, truth, true, typeof(BatchClaimDefinition).Assembly);
        Assert.True(check.Success, check.Error + check.Output);
        var canonical = DagRenderCommand.Run(batch.Root, truth, false, typeof(BatchClaimDefinition).Assembly);
        Assert.True(canonical.Success, canonical.Error + canonical.Output);
        Assert.Equal(emittedGraph, TemporaryFileSystem.File.ReadAllBytes(graphPath));
        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
    }

    [Theory]
    [InlineData(FrozenPath, 3)]
    [InlineData("D5/S0/Carrier/Probe.lean", 3)]
    [InlineData(ProblemPath, 3)]
    [InlineData(FrozenPath, 4)]
    [InlineData("D5/S0/Carrier/Probe.lean", 4)]
    [InlineData(ProblemPath, 4)]
    public void FinalEmissionRejectsChangedAuthoritativeInputs(string changedPath, int discovery)
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var calls = 0;
        BatchClaimDefinition.Creating.Value = () =>
        {
            if (++calls == discovery)
                TemporaryFileSystem.File.AppendAllText(Path.Combine(world.Root, changedPath), "\n");
        };
        try
        {
            var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));

            output.WriteLine(result.Output + result.Error);
            output.WriteLine("AUTHORITATIVE_MUTATION path={0} trigger={1} discoveries={2}", changedPath, discovery, calls);
            Assert.Equal(discovery, calls);
            Assert.Equal(1, result.ExitCode);
            Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
            Assert.Contains("shared cover context changed: " + changedPath, result.Error, StringComparison.Ordinal);
            Assert.Single(world.Entry(First).Coverage);
            Assert.Single(world.Entry(Second).Coverage);
            Assert.Equal(discovery == 4, TemporaryFileSystem.File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
            if (discovery == 4)
                Assert.Contains("Generated/DAG.md", result.Output, StringComparison.Ordinal);
        }
        finally
        {
            BatchClaimDefinition.Creating.Value = null;
        }
    }

    [Fact]
    public void FinalDagRejectsChangedCommittedLedger()
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var calls = 0;
        string? changedPath = null;
        BatchClaimDefinition.Creating.Value = () =>
        {
            if (++calls != 4) return;
            changedPath = world.LedgerPaths().Single(path => path.EndsWith(Second + ".yaml", StringComparison.Ordinal));
            TemporaryFileSystem.File.AppendAllText(changedPath, "# concurrent ledger edit\n");
        };
        try
        {
            var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));

            output.WriteLine(result.Output + result.Error);
            output.WriteLine("LEDGER_MUTATION trigger=4 discoveries={0}", calls);
            Assert.Equal(4, calls);
            Assert.NotNull(changedPath);
            Assert.Equal(1, result.ExitCode);
            Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
            Assert.Contains("ledger changed under us", result.Error, StringComparison.Ordinal);
            Assert.Single(world.Entry(First).Coverage);
            Assert.Single(world.Entry(Second).Coverage);
            Assert.EndsWith("# concurrent ledger edit\n", TemporaryFileSystem.File.ReadAllText(changedPath), StringComparison.Ordinal);
            Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(world.Root, "Generated/DAG.md")));
            Assert.Contains("Generated/DAG.md", result.Output, StringComparison.Ordinal);
        }
        finally
        {
            BatchClaimDefinition.Creating.Value = null;
        }
    }

    [Theory]
    [InlineData("Golden/values-kernels.toml", "values emit failed")]
    [InlineData("Meta/FILEMAP.toml", "filemap emit failed")]
    public void ProducerFailureKeepsCoverageAndEarlierProducerOutputs(string failedInput, string diagnostic)
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(world.Root, failedInput), "malformed input\n");
        world.WriteReportBundle();

        var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));

        output.WriteLine(result.Output + result.Error);
        Assert.Equal(1, result.ExitCode);
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Contains(diagnostic, result.Error, StringComparison.Ordinal);
        Assert.Single(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
        Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(world.Root, "tools/Generated/scribe-emissions.v1.json")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
        if (failedInput == "Meta/FILEMAP.toml")
            Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(world.Root, CanonicalValuesWriter.RelativePath)));
    }

    [Fact]
    public void CompleteBatchRetainsCapturedReportWhenOriginalBundleChanges()
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        var reportPath = world.WriteReportBundle();
        var calls = 0;
        BatchClaimDefinition.Creating.Value = () =>
        {
            if (++calls != 1) return;
            TemporaryFileSystem.File.WriteAllText(reportPath, "replaced report\n");
            TemporaryFileSystem.File.WriteAllText(reportPath + ".sha256", "replaced sidecar\n");
            TemporaryFileSystem.File.WriteAllText(reportPath + ".materials.zip", "replaced materials\n");
        };
        try
        {
            using var reports = new ReportLoadCounter();
            var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));

            Assert.True(result.Success, result.Error + result.Output);
            Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
            Assert.Equal(1, reports.Loads);
            Assert.Equal("replaced report\n", TemporaryFileSystem.File.ReadAllText(reportPath));
            Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
        }
        finally
        {
            BatchClaimDefinition.Creating.Value = null;
        }
    }

    [Theory]
    [InlineData(".provenance.json")]
    [InlineData(".input.attestation")]
    [InlineData("sha-drift")]
    [InlineData("producer-drift")]
    public void RealFinalEmissionRejectsBadBundlesAfterKeepingSuccessfulCoverage(string failure)
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        var report = world.WriteReportBundle();
        if (failure.StartsWith(".", StringComparison.Ordinal))
            TemporaryFileSystem.File.Delete(report + failure);
        else if (failure == "sha-drift")
            TemporaryFileSystem.File.WriteAllText(report + ".sha256", new string('0', 64) + "  " + Path.GetFileName(report) + "\n");
        else
        {
            var path = report + ".input.attestation";
            var lines = TemporaryFileSystem.File.ReadAllText(path).Split('\n');
            lines[2] = "producer_sha256=" + new string('0', 64);
            TemporaryFileSystem.File.WriteAllText(path, string.Join('\n', lines));
        }

        var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));

        output.WriteLine(result.Output + result.Error);
        Assert.Equal(1, result.ExitCode);
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Contains("COVER_BATCH_EMIT_FAILED", result.Error, StringComparison.Ordinal);
        Assert.Contains(failure.StartsWith(".", StringComparison.Ordinal) ? "incomplete" : "stale",
            result.Error, StringComparison.Ordinal);
        Assert.Single(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
    }

    private static void WriteEmissionInputs(string root)
    {
        WriteProblem(root);
        WriteScribeFixture(root, "Trureturing.lean", "-- synthetic root module\n");
        LeanReportInputScriptTests.CopyBatchProducerInputs(root);
        WriteScribeFixture(root, ".gitignore", ".lake/\nGenerated/\ntools/Generated/scribe-emissions.v1.json\n");
        WriteScribeFixture(root, "Blueprint/D5/S0/Carrier/Probe.md", "old blueprint projection\n");
        WriteScribeFixture(root, CanonicalValuesWriter.RelativePath, "old values projection\n");
        foreach (var path in CanonicalValuesWriter.InputPaths)
        {
            if (!TemporaryFileSystem.File.Exists(Path.Combine(root, path)))
                WriteScribeFixture(root, path, "-- synthetic producer input\n");
        }
        WriteScribeFixture(root, "Golden/values-kernels.toml", """
            schema_version = 1
            [[constants]]
            id = "D5/Synthetic"
            lean_gid = "D5/S3/Constants/Values.synthetic"
            lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
            status = "registered-open"
            definition = "synthetic registered value"
            method = "registered-open"
            reference_value = "0"
            reference_error = "0"
            open_reason = "synthetic value is not computed"
            refs = {}
            computation = "none"
            """ + "\n");
        WriteScribeFixture(root, "Meta/FILEMAP.toml",
            File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/FILEMAP.toml")));
    }

    private sealed class ReportLoadCounter : IDisposable
    {
        private readonly Action? previous = RawLeanReportArtifact.Reading.Value;
        internal int Loads { get; private set; }
        internal ReportLoadCounter() => RawLeanReportArtifact.Reading.Value = () => Loads++;
        public void Dispose() => RawLeanReportArtifact.Reading.Value = previous;
    }
}
