using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.CoverBatch.Tests;

public sealed partial class CoverBatchCommandTests
{
    [Fact]
    public void ProducerRuntimeFilesAreIgnoredWhileTrackedSourcesRequireStrictUtf8()
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        const string runtimePath = "tools/scripts/report/__pycache__/dependency.pyc";
        var runtimeFile = Path.Combine(world.Root, runtimePath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(runtimeFile)!);
        TemporaryFileSystem.File.WriteAllBytes(runtimeFile, [0xff]);

        world.WriteReportBundle();

        Assert.DoesNotContain(world.Repository.ReadCurrent().Entries, entry => entry.Path == runtimePath);
        const string sourcePath = "tools/StrataLint.Cli/Program.cs";
        TemporaryFileSystem.File.WriteAllBytes(Path.Combine(world.Root, sourcePath), [0xff]);
        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(
            SnapshotDecoder.Decode(world.Repository.ReadCurrent()));
        Assert.Equal("Repository file must be strict UTF-8: " + sourcePath + ".", failure.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CompleteProducerPipelineSharesInputsAndPreservesLedgerBytes(bool partialFailure)
    {
        using var sequential = new BatchWorld();
        WriteProblem(sequential.Root);
        sequential.RunSingles();
        using var batch = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(batch.Root);
        var reportPath = batch.WriteReportBundle();
        foreach (var path in new[] { "Blueprint/D5/S0/Carrier/Probe.md", CanonicalValuesWriter.RelativePath })
        {
            TestGit.Run(batch.Root, "ls-files", "--error-unmatch", path);
            TemporaryFileSystem.File.Delete(Path.Combine(batch.Root, path));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(batch.Root, path)));
        }
        var input = Row(First, Gid) + (partialFailure ? Row("missing-atom", Gid) : "") + Row(Second, OtherGid);
        FrozenLoadCounter frozen;
        LedgerLoadCounter ledger;
        ReportLoadCounter reports;
        CommandResult result;
        using (frozen = new FrozenLoadCounter())
        using (ledger = new LedgerLoadCounter())
        using (reports = new ReportLoadCounter())
            result = batch.RunProducers(input);

        output.WriteLine(result.Output + result.Error);
        Assert.Equal(partialFailure ? 1 : 0, result.ExitCode);
        Assert.Equal(partialFailure ? ["applied", "failed", "applied"] : ["applied", "applied"],
            Results(result).Select(item => item.Status).ToArray());
        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
        Assert.Empty(result.Error);
        Assert.False(File.Exists(Path.Combine(batch.Root, "Blueprint/D5/S0/Carrier/Probe.md")));
        foreach (var path in new[] { CanonicalValuesWriter.RelativePath })
        {
            Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(batch.Root, path)));
            Assert.Single(result.Output.Split('\n'), line => line.Contains(path, StringComparison.Ordinal));
        }
        Assert.Equal(1, reports.Loads);
        Assert.Equal(1, frozen.Catalogs);
        Assert.Equal(1, frozen.Indexes);
        Assert.Equal(0, ledger.BaselineLoads);
        Assert.Equal([1, 1], ledger.CandidateSnapshotLoads);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(batch.Root, "Generated/DAG.md")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(batch.Root, "Generated/FILEMAP.md")));
        output.WriteLine("COMPLETE_PRODUCERS synthetic_definitions=true report={0} catalog={1} index={2} baseline={3} candidate=[{4}]",
            reports.Loads, frozen.Catalogs, frozen.Indexes, ledger.BaselineLoads,
            string.Join(',', ledger.CandidateSnapshotLoads));
        Assert.True(TemporaryFileSystem.File.Exists(reportPath));

        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
    }

    [Theory]
    [InlineData("Golden/values-kernels.toml", "values emit failed")]
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
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(world.Root, "tools/Generated/scribe-emissions.v1.json")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
    }

    [Fact]
    public void CompleteBatchRetainsCapturedReportWhenOriginalBundleChanges()
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        var reportPath = world.WriteReportBundle();
        var loads = 0;
        var previous = BackfillInventoryLoader.DocumentLoading.Value;
        // The second ledger load belongs to the second item, after the report was read.
        BackfillInventoryLoader.DocumentLoading.Value = (_, _) =>
        {
            if (++loads != 2) return;
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
        }
        finally
        {
            BackfillInventoryLoader.DocumentLoading.Value = previous;
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
        TemporaryFileSystem.File.Delete(Path.Combine(root, ScribeEmissionAttestation.RelativePath));
        WriteProblem(root);
        WriteScribeFixture(root, "Trureturing.lean", "-- synthetic root module\n");
        WriteScribeFixture(root, ".gitignore",
            File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".gitignore")));
        WriteScribeFixture(root, "Blueprint/D5/S0/Carrier/Probe.md", "old blueprint projection\n");
        WriteScribeFixture(root, CanonicalValuesWriter.RelativePath, "old values projection\n");
        WriteValuesInputs(root);
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var documents = FileMapDocuments.Resolve(
            File.ReadAllBytes(Path.Combine(repositoryRoot, AdmissionPlanePolicy.FileMapPath)),
            AdmissionPlanePolicy.FileMapPath,
            path => File.ReadAllBytes(Path.Combine(repositoryRoot, path)));
        foreach (var document in documents)
            WriteScribeFixture(root, document.Path, Encoding.UTF8.GetString(document.Bytes.AsSpan()));
    }

    private static void WriteValuesInputs(string root)
    {
        foreach (var path in CanonicalValuesWriter.InputPaths)
        {
            if (!TemporaryFileSystem.File.Exists(Path.Combine(root, path)))
                WriteScribeFixture(root, path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
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
    }

    private sealed class ReportLoadCounter : IDisposable
    {
        private readonly Action? previous = RawLeanReportArtifact.Reading.Value;
        internal int Loads { get; private set; }
        internal ReportLoadCounter() => RawLeanReportArtifact.Reading.Value = () => Loads++;
        public void Dispose() => RawLeanReportArtifact.Reading.Value = previous;
    }
}
