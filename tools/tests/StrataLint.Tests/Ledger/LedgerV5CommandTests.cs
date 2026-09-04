using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerV5CommandTests
{
    [Fact]
    public void LedgerAppendWritesMatchingEventAndStateFragment()
    {
        using var temporary = new TemporaryDirectory();
        const string modulePath = "D5/S0/Carrier/A.lean";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [modulePath] = "theorem a : True := by trivial\n",
            ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            ["lakefile.toml"] = "name = \"Fixture\"\n",
            ["lake-manifest.json"] = "{}\n",
        };
        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [modulePath] = new LeanFileReport(
                [],
                [new LeanDeclaration("a", "theorem", "True", [])]),
        });
        var reportPath = Path.Combine(temporary.Path, "candidate-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, report);
        var accepted = Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(accepted);
        var repository = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(modulePath, RawChangeKind.Added)]),
            raw,
            null);

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            repository,
            ["--candidate-lean-report", reportPath]);

        Assert.True(result.Success, result.Error);
        var eventFile = Assert.Single(DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(accepted));
        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadFiles([eventFile]));
        var freeze = Assert.Single(loaded.Events);
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(modulePath));
        var stateFile = Path.Combine(
            temporary.Path,
            statePath.Value.Replace('/', Path.DirectorySeparatorChar));
        Assert.True(File.Exists(stateFile));
        var state = FrozenStateRecordLoader.Load(new RepositoryFile(
            statePath,
            ImmutableArray.CreateRange(File.ReadAllBytes(stateFile)),
            File.ReadAllText(stateFile, Encoding.UTF8)));
        Assert.Equal(
            freeze.Payload.GetProperty("statement_id").GetString(),
            state.StatementId.Value);
    }

    [Fact]
    public void SnapshotReplacementRemovesRevokedFreezeFiles()
    {
        using var temporary = new TemporaryDirectory();
        var files = EventFiles(BuildCatalog(Module("A"), Module("B", imports: ["A"])));
        var ledgerPath = Path.Combine(temporary.Path, "accepted");
        WriteLedgerDirectory(ledgerPath, files);

        DagLedgerAppendWriter.ReplaceEventFiles(ledgerPath, [files[1]], files);

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        Assert.Single(persisted);
        Assert.Equal(files[1].Path, persisted[0].Path);
    }

    [Fact]
    public void SnapshotReplacementRestoresOriginalFilesWhenPublicationFails()
    {
        using var temporary = new TemporaryDirectory();
        var files = EventFiles(BuildCatalog(Module("A"), Module("B")));
        var ledgerPath = Path.Combine(temporary.Path, "accepted");
        WriteLedgerDirectory(ledgerPath, files);
        var colliding = new RepositoryFile(
            RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/.ledger-write.lock"),
            ImmutableArray.Create<byte>(1),
            "\u0001");

        Assert.Throws<IOException>(() =>
            DagLedgerAppendWriter.ReplaceEventFiles(ledgerPath, [colliding], files));

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath)
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(
            files.Select(static file => file.Path)
                .OrderBy(static path => path.Value, StringComparer.Ordinal),
            persisted.Select(static file => file.Path));
        Assert.All(persisted, actual => Assert.True(
            files.Single(expected => expected.Path == actual.Path)
                .RawBytes.AsSpan().SequenceEqual(actual.RawBytes.AsSpan())));
    }
}
