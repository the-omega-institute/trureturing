using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerRevokeCommandTests
{
    [Fact]
    public void ProductionCommandAppendsAValidatedRevokeWithoutRewritingHistory()
    {
        using var fixture = new LedgerRevokeFixture();
        var before = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath)
            .ToDictionary(static file => file.Path, static file => file.RawBytes);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "ledger-revoke",
                "--candidate-lean-report",
                fixture.ReportPath,
                "--receipt-blob-oid",
                fixture.ReceiptBlobOid,
            ],
            fixture.Environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains("appended_revokes=1", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
        var files = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Equal(before.Count + 1, files.Length);
        Assert.All(before, item => Assert.True(
            files.Single(file => file.Path == item.Key).RawBytes.AsSpan().SequenceEqual(item.Value.AsSpan())));
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));
        Assert.Empty(view.ActiveByCase);
        Assert.Single(view.Events, static item => item.EventType == "Revoke");
    }

    private sealed class LedgerRevokeFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerRevokeFixture()
        {
            var module = ModuleWithReport("A", "theorem a : True := by trivial\n", "True");
            var baselineCatalog = BuildCatalog(module);
            var baselineFiles = EventFiles(baselineCatalog);
            var baseline = Baseline(baselineCatalog);
            var node = Assert.Single(baseline.ActiveFrozenNodes);
            var provisional = new RevocationEvidence.KernelWitnessFailure(
                node.FrozenNodeId,
                node.WitnessId,
                string.Empty,
                string.Empty);
            var receiptBytes = RevocationReceiptWriter.Write(baseline, provisional);
            var receiptText = Encoding.UTF8.GetString(receiptBytes.AsSpan());
            ReceiptBlobOid = GitBlobOid(receiptText);

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Evidence/D5/A.run.json"] = receiptText,
                ["lake-manifest.json"] = "{}\n",
                ["lakefile.toml"] = "[package]\nname = \"fixture\"\n",
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            };
            AddLedgerFiles(files, baselineFiles);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => new RawRepositoryEntry(
                    item.Key,
                    ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(item.Value)),
                    GitBlobOid(item.Value))));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            WriteLedgerDirectory(LedgerPath, baselineFiles);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, report);
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
                new FakeLeanReportSource(null));
        }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string ReceiptBlobOid { get; }

        internal string ReportPath { get; }

        public void Dispose() => temporary.Dispose();

    }
}
