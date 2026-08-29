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

        var failure = ValidateAdmissionReplacementFiles(
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

        var failure = ValidateAdmissionReplacementFiles(
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

        var failure = ValidateAdmissionReplacementFiles(
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
        var legacyA = LegacyFileForModule(legacyFiles, "A");
        var legacyB = LegacyFileForModule(legacyFiles, "B");
        var v5A = Assert.Single(EventFiles(BuildCatalog(Module("A"))));
        var candidateFiles = ImmutableArray.Create(
            WithBytesAtSamePath(legacyB, Assert.Single(EventFiles(BuildCatalog(Module("B"))))),
            v5A);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (legacyA.Path.Value, RawChangeKind.Deleted),
            (legacyB.Path.Value, RawChangeKind.Modified),
            (v5A.Path.Value, RawChangeKind.Added),
        ]);

        var preparation = Prepare(legacyFiles, candidateFiles, changes);
        var failure = ValidatePreparedAdmissionReplacement(preparation, changes, catalog);

        Assert.Null(preparation.Replacement);
        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsReplacementWhenRetainedAndNewFreezeCoverSameModule()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var retainedA = LegacyFileForModule(legacyFiles, "A");
        var legacyB = LegacyFileForModule(legacyFiles, "B");
        var v5Files = EventFiles(catalog);
        var candidateFiles = ImmutableArray.Create(retainedA).AddRange(v5Files);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (legacyB.Path.Value, RawChangeKind.Deleted),
            .. v5Files.Select(static file => (file.Path.Value, RawChangeKind.Added)),
        ]);

        var preparation = Prepare(legacyFiles, candidateFiles, changes);
        var failure = ValidatePreparedAdmissionReplacement(preparation, changes, catalog);

        Assert.Null(preparation.Replacement);
        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionRejectsReplacementWhenDeletedModulesAreProperSubsetOfUnretainedBaseModules()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"), Module("C"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var retainedA = LegacyFileForModule(legacyFiles, "A");
        var legacyB = LegacyFileForModule(legacyFiles, "B");
        var legacyC = LegacyFileForModule(legacyFiles, "C");
        var v5B = Assert.Single(EventFiles(BuildCatalog(Module("B"))));
        var v5C = Assert.Single(EventFiles(BuildCatalog(Module("C"))));
        var candidateFiles = ImmutableArray.Create(
            retainedA,
            WithBytesAtSamePath(legacyC, v5C),
            v5B);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (legacyB.Path.Value, RawChangeKind.Deleted),
            (legacyC.Path.Value, RawChangeKind.Modified),
            (v5B.Path.Value, RawChangeKind.Added),
        ]);

        var preparation = Prepare(legacyFiles, candidateFiles, changes);
        var failure = ValidatePreparedAdmissionReplacement(preparation, changes, catalog);

        Assert.Null(preparation.Replacement);
        AssertReuseRejected(failure);
    }

    [Fact]
    public void AdmissionAllowsLegacyReplacementWithRetainedDisjointModules()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var legacyFiles = LegacyEventFiles(catalog, schemaVersion: 4);
        var retainedA = LegacyFileForModule(legacyFiles, "A");
        var legacyB = LegacyFileForModule(legacyFiles, "B");
        var v5B = Assert.Single(EventFiles(BuildCatalog(Module("B"))));
        var candidateFiles = ImmutableArray.Create(retainedA, v5B);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (legacyB.Path.Value, RawChangeKind.Deleted),
            (v5B.Path.Value, RawChangeKind.Added),
        ]);

        var preparation = Prepare(legacyFiles, candidateFiles, changes);
        var failure = ValidatePreparedAdmissionReplacement(preparation, changes, catalog);

        Assert.NotNull(preparation.Replacement);
        Assert.Null(failure);
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

        var failure = ValidateAdmissionReplacementFiles(
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

        var failure = ValidateAdmissionReplacementFiles(
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

        var failure = ValidateAdmissionReplacementFiles(
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

        var preparation = Prepare(legacyFiles, v5Files, changes);
        var recognition = preparation.Replacement;
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

    private static FrozenLedgerAdmissionFailure? ValidateAdmissionReplacementFiles(
        ImmutableArray<RepositoryFile> baseFiles,
        ImmutableArray<RepositoryFile> candidateFiles,
        RawChangeSet changes,
        FrozenMaterialCatalog catalog) =>
        ValidatePreparedAdmissionReplacement(
            Prepare(baseFiles, candidateFiles, changes),
            changes,
            catalog);

    private static FrozenLedgerAdmissionFailure? ValidatePreparedAdmissionReplacement(
        FrozenLedgerAdmissionPreparation preparation,
        RawChangeSet changes,
        FrozenMaterialCatalog catalog)
    {
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

    private static RepositoryFile LegacyFileForModule(
        ImmutableArray<RepositoryFile> files,
        string module) =>
        files.Single(file => FrozenLedgerBaseViewReader.Read(Snapshot([file]))
            .ActiveByPath.ContainsKey(RepoPathFor(module)));

    private static RepositoryFile WithBytesAtSamePath(
        RepositoryFile pathSource,
        RepositoryFile contentSource) =>
        new(
            pathSource.Path,
            contentSource.RawBytes,
            contentSource.Text);

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
