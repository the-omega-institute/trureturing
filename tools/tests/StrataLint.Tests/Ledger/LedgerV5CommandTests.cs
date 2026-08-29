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
    public void EntirelyLegacyLedgerUpgradesWhenCommittedFreezeStatementIdentitiesMatch()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = LegacyUpgradeFixture(temporary.Path);

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            fixture.Gateway,
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Single(persisted);
        Assert.All(persisted, static file => Assert.Equal(
            5,
            System.Text.Json.JsonDocument.Parse(file.RawBytes.ToArray())
                .RootElement.GetProperty("schema_version").GetInt32()));
    }

    [Fact]
    public void EntirelyLegacyLedgerRejectsChangedStatementIdentity()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = LegacyUpgradeFixture(
            temporary.Path,
            legacyStatementId: Sha256("retired statement identity"));

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            fixture.Gateway,
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EntirelyLegacyLedgerRejectsChangedDeclarationStatementIdentity()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = LegacyUpgradeFixture(
            temporary.Path,
            legacyDeclarationStatementId: Sha256("retired declaration identity"));

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            fixture.Gateway,
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success);
        Assert.Contains(PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EntirelyLegacyLedgerRejectsWorkingTreeBytesOutsideTheCommittedBaseline()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = LegacyUpgradeFixture(
            temporary.Path,
            committedLegacyStatementId: Sha256("different committed legacy identity"));

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            fixture.Gateway,
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success);
        Assert.Contains("does not match the committed baseline", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RerunLedgerAppendReplacesAnInflightV4ShardWithoutHumanSelection()
    {
        using var temporary = new TemporaryDirectory();
        var baselineCatalog = BuildCatalog(Module("A"));
        var baselineFiles = EventFiles(baselineCatalog);
        var candidateCatalog = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var candidateB = candidateCatalog.ByPath[RepoPathFor("B")];
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            ["lakefile.toml"] = "[package]\nname = \"fixture\"\n",
            ["lake-manifest.json"] = "{}\n",
            [PathFor("A")] = "theorem a : True := by trivial\n",
            [PathFor("B")] = "import D5.S0.Carrier.A\ntheorem b : True := by trivial\n",
        };
        AddLedgerFiles(files, baselineFiles);
        var legacyHash = Sha256("inflight-v4-event");
        var legacyPath = $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{legacyHash[7..]}.json";
        files[legacyPath] =
            $"{{\"event_hash\":\"{legacyHash}\",\"event_type\":\"Freeze\","
            + "\"payload\":{},\"schema_version\":4}\n";
        var raw = RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [PathFor("A")] = Report("A"),
            [PathFor("B")] = Report("B", ["D5.S0.Carrier.A"]),
        });
        var reportPath = Path.Combine(temporary.Path, "report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, report);
        var ledgerPath = Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        WriteLedgerDirectory(ledgerPath, baselineFiles);
        File.WriteAllText(Path.Combine(ledgerPath, Path.GetFileName(legacyPath)), files[legacyPath]);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
            [
                (PathFor("B"), RawChangeKind.Added),
                (legacyPath, RawChangeKind.Added),
            ]),
            raw,
            baseline: null);

        var result = DagLedgerAppendWriter.Append(
            temporary.Path,
            gateway,
            ["--candidate-lean-report", reportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        Assert.Equal(2, persisted.Length);
        Assert.All(persisted, static file => Assert.Equal(
            5,
            System.Text.Json.JsonDocument.Parse(file.RawBytes.ToArray())
                .RootElement.GetProperty("schema_version").GetInt32()));
        Assert.Equal(
            candidateB.StatementId,
            FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
                persisted.ToImmutableDictionary(static file => file.Path)))
                .ActiveByPath[RepoPathFor("B")].Material.StatementId);
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

    private static LeanFileReport Report(string name, ImmutableArray<string> imports = default) =>
        new(
            imports.IsDefault ? ImmutableArray<string>.Empty : imports,
            [
                new LeanDeclaration(
                    name.ToLowerInvariant(),
                    "theorem",
                    "True",
                    ImmutableArray<string>.Empty)
                {
                    NameKey = $"ns(n0,{name.Length}:{name.ToLowerInvariant()})",
                },
            ]);

    private static LegacyUpgradeTestFixture LegacyUpgradeFixture(
        string repositoryRoot,
        string? legacyStatementId = null,
        string? committedLegacyStatementId = null,
        string? legacyDeclarationStatementId = null)
    {
        var catalog = BuildCatalog(Module("A"));
        var material = Assert.Single(catalog.ClosedNodes);
        var legacyHash = Sha256("committed legacy Freeze for A");
        var legacyPath = $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{legacyHash[7..]}.json";
        var legacyText = LegacyFreezeText(
            material,
            legacyHash,
            legacyStatementId,
            legacyDeclarationStatementId);
        var committedLegacyText = LegacyFreezeText(
            material,
            legacyHash,
            committedLegacyStatementId ?? legacyStatementId,
            legacyDeclarationStatementId);
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
            ["lakefile.toml"] = "[package]\nname = \"fixture\"\n",
            ["lake-manifest.json"] = "{}\n",
            [PathFor("A")] = "theorem a : True := by trivial\n",
            [legacyPath] = legacyText,
        };
        var raw = RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
        var committedFiles = new Dictionary<string, string>(files, StringComparer.Ordinal)
        {
            [legacyPath] = committedLegacyText,
        };
        var committedRaw = RawRepositorySnapshot.Create(
            committedFiles.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var reportPath = Path.Combine(repositoryRoot, "report.json");
        RawLeanReportArtifact.WriteFile(
            reportPath,
            snapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [PathFor("A")] = Report("A"),
            }));
        var ledgerPath = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(ledgerPath);
        File.WriteAllText(Path.Combine(ledgerPath, Path.GetFileName(legacyPath)), legacyText);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(legacyPath, RawChangeKind.Modified)]),
            raw,
            committedRaw);
        return new LegacyUpgradeTestFixture(gateway, reportPath, ledgerPath);
    }

    private static string LegacyFreezeText(
        FrozenNodeMaterial material,
        string eventHash,
        string? statementId,
        string? declarationStatementId = null) =>
        JsonSerializer.Serialize(new
        {
            event_hash = eventHash,
            event_type = "Freeze",
            payload = new
            {
                declaration_statement_ids = material.DeclarationStatementIds.Select(item => new
                {
                    declaration_name_key = item.DeclarationNameKey,
                    kind = item.Kind,
                    statement_id = declarationStatementId ?? item.StatementId.Value,
                }),
                input = new
                {
                    descriptor_selector = material.RepoPath.Value,
                },
                prerequisite_frozen_node_ids = material.PrerequisiteFrozenNodeIds.Select(static item => item.Value),
                statement_id = statementId ?? material.StatementId.Value,
            },
            schema_version = 4,
        }) + "\n";

    private sealed record LegacyUpgradeTestFixture(
        FakeRepositoryGateway Gateway,
        string ReportPath,
        string LedgerPath);
}
