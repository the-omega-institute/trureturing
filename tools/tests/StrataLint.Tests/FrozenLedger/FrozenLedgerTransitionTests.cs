using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void HistoricalV4FreezeLoadedThroughAcceptedEventLoaderWithMatchingStatementIdentityIsAccepted()
    {
        var catalog = BuildCatalog(Module("A"));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistoryAfterTrustedAcceptedEventLoad(
                LegacyEventFiles(catalog, schemaVersion: 4),
                catalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    public void HistoricalV2AndV3FreezesLoadedThroughAcceptedEventLoaderAreAccepted(int schemaVersion)
    {
        var catalog = BuildCatalog(Module("A"));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistoryAfterTrustedAcceptedEventLoad(
                LegacyEventFiles(catalog, schemaVersion),
                catalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void HistoricalV4FreezeLoadedThroughAcceptedEventLoaderWithChangedStatementReportsStatementIdentityChanged()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                StatementId = StatementId.Create(Sha256("rewritten statement")),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistoryAfterTrustedAcceptedEventLoad(
                LegacyEventFiles(recordedCatalog, schemaVersion: 4),
                currentCatalog));

        Assert.Contains(PathFor("A"), rejected.Message, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalV4FreezeLoadedThroughAcceptedEventLoaderWithChangedDeclarationReportsStatementIdentityChanged()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                DeclarationStatementIds = recordedMaterial.DeclarationStatementIds
                    .Select(declaration => declaration with
                    {
                        StatementId = StatementId.Create(Sha256("rewritten declaration")),
                    })
                    .ToImmutableArray(),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistoryAfterTrustedAcceptedEventLoad(
                LegacyEventFiles(recordedCatalog, schemaVersion: 4),
                currentCatalog));

        Assert.Contains(PathFor("A"), rejected.Message, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    public void LegacyNonFreezeEventsThatCannotConstructV5ViewFailClosed(int schemaVersion)
    {
        var exception = Assert.Throws<FormatException>(() =>
            FrozenLedgerBaseViewReader.ValidateTrustedPayload(
                "Reattest",
                schemaVersion,
                JsonSerializer.SerializeToElement(new { })));

        Assert.Contains(
            $"trusted Reattest schema_version {schemaVersion} cannot construct a v5 base view",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void TrustedAcceptedEventLoaderLoadsEveryAcceptedEventInMixedRepositoryLedger()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var acceptedDirectory = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        var files = Directory.EnumerateFiles(
                acceptedDirectory,
                "*.json",
                SearchOption.TopDirectoryOnly)
            .Order(StringComparer.Ordinal)
            .Select(path =>
            {
                var bytes = File.ReadAllBytes(path);
                var relativePath = Path.GetRelativePath(repositoryRoot, path)
                    .Replace(Path.DirectorySeparatorChar, '/');
                return new RepositoryFile(
                    RepoPath.CreateKnown(relativePath),
                    ImmutableArray.CreateRange(bytes),
                    Encoding.UTF8.GetString(bytes));
            })
            .ToImmutableArray();

        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadTrustedFiles(files));

        Assert.Equal(files.Length, loaded.Events.Length);
        Assert.Contains(loaded.Events, static item => item.SchemaVersion == 4);
        Assert.Contains(loaded.Events, static item =>
            item.SchemaVersion == FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion);
        Assert.All(loaded.Events, static item =>
            Assert.True(item.SchemaVersion is 4 or FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion));
    }

    [Fact]
    public void ProofBodyOnlyChangeDoesNotReportStatementIdentityChanged()
    {
        var recordedCatalog = BuildCatalog(Module(
            "A",
            source: "theorem a : True := by trivial\n"));
        var currentCatalog = BuildCatalog(Module(
            "A",
            source: "theorem a : True := by exact True.intro\n"));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void StatementChangeReportsActiveModuleStatementIdentityChanged()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                StatementId = StatementId.Create(Sha256("rewritten statement")),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains(PathFor("A"), rejected.Message, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonRejectsAddedDeclaration()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                DeclarationStatementIds = recordedMaterial.DeclarationStatementIds.Add(
                    new FrozenDeclarationStatement(
                        "ns(n0,5:extra)",
                        "theorem",
                        StatementId.Create(Sha256("added declaration")))),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonRejectsCurrentAxiomClosureOutsideStandardAllowlist()
    {
        var catalog = BuildCatalog(Module("A"));
        var material = Assert.Single(catalog.ClosedNodes) with
        {
            AxiomClosure = ["Nonstandard.axiom"],
        };
        var recordedCatalog = ReplaceMaterial(catalog, material);
        var currentCatalog = ReplaceMaterial(catalog, material);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains("standard axiom allowlist", rejected.Message, StringComparison.Ordinal);
    }

    private static FrozenMaterialCatalog ReplaceMaterial(
        FrozenMaterialCatalog catalog,
        FrozenNodeMaterial material) =>
        FrozenMaterialCatalog.Create(
            catalog.States,
            [material],
            catalog.OpenCases,
            catalog.TailRegistrations,
            catalog.Adjacency);

    private static FrozenLedgerValidationOutcome ValidateHistoryAfterTrustedAcceptedEventLoad(
        ImmutableArray<RepositoryFile> files,
        FrozenMaterialCatalog catalog)
    {
        _ = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadTrustedFiles(files));
        return ValidateHistory(files, catalog);
    }

    private static ImmutableArray<RepositoryFile> LegacyEventFiles(
        FrozenMaterialCatalog catalog,
        int schemaVersion) =>
        catalog.ClosedNodes.Select(material =>
        {
            var eventHash = Sha256(
                $"legacy v{schemaVersion} Freeze for {material.RepoPath.Value}");
            var declarations = material.DeclarationStatementIds.Select(
                static declaration => new
                {
                    declaration_name_key = declaration.DeclarationNameKey,
                    kind = declaration.Kind,
                    statement_id = declaration.StatementId.Value,
                });
            var input = new
            {
                base_commit_oid = GitOid('a'),
                base_tree_oid = GitOid('b'),
                descriptor_blob_oid = GitBlobOid(material.RepoPath.Value),
                descriptor_selector = material.RepoPath.Value,
                materializer = "repository-snapshot-v1",
                supporting_blob_oids = Array.Empty<string>(),
            };
            var prerequisites = material.PrerequisiteFrozenNodeIds.Select(
                static prerequisite => prerequisite.Value);
            var witnessId = Sha256(
                $"legacy v{schemaVersion} witness for {material.RepoPath.Value}");
            var inputFingerprint = Sha256(
                $"legacy v{schemaVersion} input for {material.RepoPath.Value}");
            var payload = JsonSerializer.SerializeToNode(new
            {
                axiom_closure = material.AxiomClosure,
                case_id = FrozenLedgerCanonicalWriter.CaseId(
                    material.RepoPath,
                    material.StatementId),
                declaration_statement_ids = declarations,
                frozen_node_id = material.FrozenNodeId.Value,
                input,
                prerequisite_frozen_node_ids = prerequisites,
                statement_id = material.StatementId.Value,
                witness_id = witnessId,
            })!.AsObject();
            switch (schemaVersion)
            {
                case 2:
                    payload.Remove("axiom_closure");
                    AddRetiredFreezeFields(payload, material, inputFingerprint);
                    break;
                case 3:
                    AddRetiredFreezeFields(payload, material, inputFingerprint);
                    break;
                case 4:
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(schemaVersion));
            }

            var envelope = JsonSerializer.Serialize(new
            {
                event_hash = eventHash,
                event_type = "Freeze",
                payload,
                schema_version = schemaVersion,
            }) + "\n";
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(eventHash);
            return new RepositoryFile(
                RepoPath.CreateKnown(
                    $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json"),
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(envelope)),
                envelope);
        }).ToImmutableArray();

    private static void AddRetiredFreezeFields(
        JsonObject payload,
        FrozenNodeMaterial material,
        string inputFingerprint)
    {
        payload["case_class"] = "active-frozen";
        payload["evaluation"] = "admission";
        payload["expected"] = JsonSerializer.SerializeToNode(new
        {
            allowed_dispositions = new[] { "admit" },
            diagnostic_match = "none",
            required_diagnostics = Array.Empty<string>(),
        });
        payload["input_fingerprint"] = inputFingerprint;
        payload["node_path"] = material.RepoPath.Value;
        payload["semantic_receipt"] = material.FrozenNodeId.Value;
        payload["truth_state"] = "Closed";
    }

}
