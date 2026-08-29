using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void AdmissionAllowsEntireLegacyLedgerReplacementWhenAllThreeConjunctsHold()
    {
        var catalog = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var v5Files = EventFiles(catalog);

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            v5Files,
            EntireReplacementChanges(legacyFiles, v5Files),
            catalog);

        Assert.Null(failure);
    }

    [Fact]
    public void AdmissionAllowsNewClosedModuleAlongsideAuthorizedLegacyReplacement()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var candidateCatalog = BuildCatalog(Module("A"), Module("B"));
        var legacyFiles = LegacyEventFiles(recordedCatalog, schemaVersion: 4);
        var v5Files = EventFiles(candidateCatalog);

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            v5Files,
            EntireReplacementChanges(legacyFiles, v5Files),
            candidateCatalog);

        Assert.Null(failure);
    }

    [Fact]
    public void AdmissionRejectsEntireReplacementWhenBaseContainsV5Event()
    {
        var catalogA = BuildCatalog(Module("A"));
        var catalogB = BuildCatalog(Module("B"));
        var candidateCatalog = BuildCatalog(Module("A"), Module("B"));
        var baseFiles = LegacyEventFiles(catalogA, schemaVersion: 4)
            .Add(WithHistoricalEventHash(Assert.Single(EventFiles(catalogB)), "mixed v5 base"));
        var v5Files = EventFiles(candidateCatalog);

        var failure = ValidateAdmissionReplacement(
            baseFiles,
            v5Files,
            EntireReplacementChanges(baseFiles, v5Files),
            candidateCatalog);

        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsPartialAcceptedLedgerReplacement()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var legacyA = legacyFiles.Single(file =>
            FrozenLedgerBaseViewReader.Read(Snapshot([file])).ActiveByPath.ContainsKey(RepoPathFor("A")));
        var retainedLegacy = legacyFiles.Single(file => file.Path != legacyA.Path);
        var v5A = Assert.Single(EventFiles(BuildCatalog(Module("A"))));
        var candidateFiles = ImmutableArray.Create(retainedLegacy, v5A);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (legacyA.Path.Value, RawChangeKind.Deleted),
            (v5A.Path.Value, RawChangeKind.Added),
        ]);

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            candidateFiles,
            changes,
            catalog);

        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsEntireLegacyReplacementWhenStatementIdentityChanges()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var candidateCatalog = BuildCatalog(ModuleWithReport(
            "A",
            "theorem a : True := by trivial\n",
            statementMaterial: "changed proposition"));
        var legacyFiles = LegacyEventFiles(recordedCatalog, schemaVersion: 4);
        var v5Files = EventFiles(candidateCatalog);

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            v5Files,
            EntireReplacementChanges(legacyFiles, v5Files),
            candidateCatalog);

        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsEntireLegacyReplacementWhenDeclarationStatementIdentityChanges()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var candidateCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                DeclarationStatementIds = recordedMaterial.DeclarationStatementIds
                    .Select(declaration => declaration with
                    {
                        StatementId = StatementId.Create(Sha256("changed declaration")),
                    })
                    .ToImmutableArray(),
            });
        var legacyFiles = LegacyEventFiles(recordedCatalog, schemaVersion: 4);
        var v5Files = EventFiles(candidateCatalog);

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            v5Files,
            EntireReplacementChanges(legacyFiles, v5Files),
            candidateCatalog);

        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsOrdinaryFreezePathReuseOutsideEntireReplacement()
    {
        var catalog = BuildCatalog(Module("A"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var v5Files = EventFiles(catalog);
        var candidateFiles = legacyFiles.AddRange(v5Files);
        var changes = RawChangeSet.CreateWithKinds(
            v5Files.Select(static file => (file.Path.Value, RawChangeKind.Added)));

        var failure = ValidateAdmissionReplacement(
            legacyFiles,
            candidateFiles,
            changes,
            catalog);

        AssertReuseRejected(failure);
    }

    [Fact]
    public void EntireReplacementRecognitionIsIndependentFromInjectedAuthorization()
    {
        var catalog = BuildCatalog(Module("A"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var v5Files = EventFiles(catalog);
        var changes = EntireReplacementChanges(legacyFiles, v5Files);
        var baseView = FrozenLedgerBaseViewReader.Read(Snapshot(legacyFiles));

        var recognition = FrozenLedgerReplacementRecognition.Recognize(baseView, changes);
        var preparation = Prepare(legacyFiles, v5Files, changes);
        var scope = FrozenLedgerAdmissionScope.Create(
            changes,
            preparation,
            catalog.States,
            catalog.Adjacency);
        var denied = FrozenLedger.ValidateAdmissionDelta(
            preparation,
            scope,
            catalog,
            RejectAllReplacementAuthorization.Instance);

        Assert.NotNull(recognition);
        AssertReuseRejected(denied);
    }

    private static FrozenLedgerAdmissionFailure? ValidateAdmissionReplacement(
        ImmutableArray<RepositoryFile> baseFiles,
        ImmutableArray<RepositoryFile> candidateFiles,
        RawChangeSet changes,
        FrozenMaterialCatalog catalog)
    {
        var preparation = Prepare(baseFiles, candidateFiles, changes);
        var scope = FrozenLedgerAdmissionScope.Create(
            changes,
            preparation,
            catalog.States,
            catalog.Adjacency);
        return FrozenLedger.ValidateAdmissionDelta(
            preparation,
            scope,
            catalog,
            LegacyFrozenLedgerReplacementAuthorization.Instance);
    }

    private static FrozenLedgerAdmissionPreparation Prepare(
        ImmutableArray<RepositoryFile> baseFiles,
        ImmutableArray<RepositoryFile> candidateFiles,
        RawChangeSet changes) =>
        new ProductionFrozenLedgerAdmissionServices(
            repositoryRoot: ".",
            ImmutableHashSet<string>.Empty)
        .Prepare(Snapshot(candidateFiles), Snapshot(baseFiles), changes);

    private static RawChangeSet EntireReplacementChanges(
        ImmutableArray<RepositoryFile> baseFiles,
        ImmutableArray<RepositoryFile> candidateFiles) =>
        RawChangeSet.CreateWithKinds(
            baseFiles.Select(static file => (file.Path.Value, RawChangeKind.Deleted))
                .Concat(candidateFiles.Select(static file =>
                    (file.Path.Value, RawChangeKind.Added))));

    private static RepositorySnapshot Snapshot(IEnumerable<RepositoryFile> files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path));

    private static RepositoryFile WithHistoricalEventHash(RepositoryFile file, string material)
    {
        using var document = JsonDocument.Parse(file.RawBytes.ToArray());
        var root = document.RootElement;
        var eventHash = Sha256(material);
        var text = JsonSerializer.Serialize(new
        {
            event_hash = eventHash,
            event_type = root.GetProperty("event_type").GetString(),
            payload = root.GetProperty("payload"),
            schema_version = root.GetProperty("schema_version").GetInt32(),
        }) + "\n";
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(eventHash);
        return new RepositoryFile(
            RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json"),
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)),
            text);
    }

    private static void AssertReuseRejected(FrozenLedgerAdmissionFailure? failure)
    {
        var rejected = Assert.IsType<FrozenLedgerAdmissionFailure>(failure);
        Assert.Contains(
            "Freeze reused an active case ID or module path",
            rejected.Message,
            StringComparison.Ordinal);
    }

    private sealed class RejectAllReplacementAuthorization : IFrozenLedgerReplacementAuthorization
    {
        internal static RejectAllReplacementAuthorization Instance { get; } = new();

        public bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context) => false;
    }
}
