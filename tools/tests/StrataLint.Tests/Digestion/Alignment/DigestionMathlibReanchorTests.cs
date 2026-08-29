using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class DigestionMathlibReanchorTests
{
    private const string ModuleAGid = "D5/S0/Carrier/A";
    private const string ModuleBGid = "D5/S0/Carrier/B";

    [Fact]
    public void PinUpgradeWithEquivalentPropositionAndStandardAxiomsReanchorsReceipt()
    {
        var fixture = CreateAuthorizedDigestionReanchorFixture();

        var reanchored = MathlibUpgradeDigestionReanchor.Apply(
            fixture.Document,
            fixture.ProtectedBase,
            fixture.Candidate,
            fixture.Changes,
            fixture.Lean);

        var receipt = Assert.Single(Assert.Single(reanchored.RequireDigestionEntries()).Receipts.Coverage);
        Assert.Equal(fixture.CandidateAStatementId, receipt.TargetStatementId);
        Assert.DoesNotContain(
            EvaluateDigestionReanchorFixture(fixture, reanchored).Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void AlignDigestionStatusUsesAuthorizedMathlibReceiptReanchor()
    {
        var fixture = CreateAuthorizedDigestionReanchorFixture();
        var currentFiles = DigestionReanchorTextDictionary(fixture.Candidate);
        var baselineFiles = DigestionReanchorTextDictionary(fixture.ProtectedBase);
        var policy = new RuleFixture();
        foreach (var path in new[] { "Meta/registry.yaml", "Meta/domains.yaml" })
        {
            currentFiles.Add(path, policy.Files[path]);
            baselineFiles.Add(path, policy.Files[path]);
        }

        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, fixture.Document);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baselineFiles, fixture.Document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                fixture.Changes,
                DigestionReanchorRawSnapshot(currentFiles),
                DigestionReanchorRawSnapshot(baselineFiles)),
            new FakeLeanReportSource(fixture.Lean.Report),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var receipt = Assert.Single(Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries()).Receipts.Coverage);
        Assert.Equal(fixture.CandidateAStatementId, receipt.TargetStatementId);
    }

    [Fact]
    public void ChangedPropositionRejectsReanchorAndKeepsReceiptMismatchFatal()
    {
        var fixture = CreateDigestionReanchorFixture(
            candidateASource: "theorem a : False := by contradiction\n",
            candidateAStatementMaterial: "new elaborated False",
            pinsChanged: true,
            candidateAAxioms: ["propext"],
            receiptGid: ModuleAGid);

        AssertRejectedDigestionReanchorRemainsFatal(fixture);
    }

    [Fact]
    public void UnchangedPinsRejectReanchorAndKeepReceiptMismatchFatal()
    {
        var fixture = CreateDigestionReanchorFixture(
            candidateASource: "theorem a : True := by trivial\n",
            candidateAStatementMaterial: "new elaborated True",
            pinsChanged: false,
            candidateAAxioms: ["propext"],
            receiptGid: ModuleAGid);

        AssertRejectedDigestionReanchorRemainsFatal(fixture);
    }

    [Fact]
    public void NonstandardAxiomRejectsReanchorAndKeepsReceiptMismatchFatal()
    {
        var fixture = CreateDigestionReanchorFixture(
            candidateASource: "theorem a : True := by trivial\n",
            candidateAStatementMaterial: "new elaborated True",
            pinsChanged: true,
            candidateAAxioms: ["Nonstandard.axiom"],
            receiptGid: ModuleAGid);

        AssertRejectedDigestionReanchorRemainsFatal(fixture);
    }

    [Fact]
    public void ReceiptOutsideDriftSetIsByteIdenticalAndMismatchRemainsFatal()
    {
        var fixture = CreateDigestionReanchorFixture(
            candidateASource: "theorem a : True := by trivial\n",
            candidateAStatementMaterial: "new elaborated True",
            pinsChanged: true,
            candidateAAxioms: ["propext"],
            receiptGid: ModuleBGid,
            receiptStatementId: FrozenStatementReceiptTestData.Id('f'));
        var before = BackfillInventoryWriter.WriteAtom(
            Assert.Single(fixture.Document.RequireDigestionEntries()));

        var reanchored = MathlibUpgradeDigestionReanchor.Apply(
            fixture.Document,
            fixture.ProtectedBase,
            fixture.Candidate,
            fixture.Changes,
            fixture.Lean);

        Assert.Equal(
            before.ToArray(),
            BackfillInventoryWriter.WriteAtom(
                Assert.Single(reanchored.RequireDigestionEntries())).ToArray());
        AssertCoverageReceiptMismatchIsFatal(fixture, reanchored);
    }

    [Fact]
    public void ReceiptNotBoundToBaselineIsNotRepairedByAuthorizedUpgrade()
    {
        var fixture = CreateDigestionReanchorFixture(
            candidateASource: "theorem a : True := by trivial\n",
            candidateAStatementMaterial: "new elaborated True",
            pinsChanged: true,
            candidateAAxioms: ["propext"],
            receiptGid: ModuleAGid,
            receiptStatementId: FrozenStatementReceiptTestData.Id('e'));

        AssertRejectedDigestionReanchorRemainsFatal(fixture);
    }

    private static DigestionReanchorFixture CreateAuthorizedDigestionReanchorFixture() =>
        CreateDigestionReanchorFixture(
            candidateASource: "theorem a : True := by trivial\n",
            candidateAStatementMaterial: "new elaborated True",
            pinsChanged: true,
            candidateAAxioms: ["propext"],
            receiptGid: ModuleAGid);

    private static DigestionReanchorFixture CreateDigestionReanchorFixture(
        string candidateASource,
        string candidateAStatementMaterial,
        bool pinsChanged,
        ImmutableArray<string> candidateAAxioms,
        string receiptGid,
        string? receiptStatementId = null)
    {
        var baseModules = new[]
        {
            ModuleWithReport(
                "A",
                "theorem a : True := by exact True.intro\n",
                statementMaterial: "old elaborated True",
                axioms: ["propext"]),
            Module("B"),
        };
        var candidateModules = new[]
        {
            ModuleWithReport(
                "A",
                candidateASource,
                candidateAStatementMaterial,
                axioms: candidateAAxioms),
            Module("B"),
        };
        var baseCatalog = BuildCatalog(baseModules);
        var candidateEventModules = candidateModules.Select(module => module.Name == "A"
                ? module with { Axioms = ["propext"] }
                : module)
            .ToArray();
        var candidateCatalog = BuildCatalog(candidateEventModules);
        var baseEvents = EventFiles(baseCatalog);
        var candidateEvents = EventFiles(candidateCatalog);
        var baseAEvent = DigestionReanchorLedgerEventFor(baseEvents, "A");
        var candidateAEvent = DigestionReanchorLedgerEventFor(candidateEvents, "A");
        var baseBEvent = DigestionReanchorLedgerEventFor(baseEvents, "B");
        var sourceBytes = Encoding.UTF8.GetBytes("digestion receipt source\n");
        var atom = new DigestionAtom(
            "manual/mathlib-reanchor",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            []);
        var oldTarget = receiptGid == ModuleAGid
            ? baseCatalog.ByPath[RepoPathFor("A")].StatementId.Value
            : baseCatalog.ByPath[RepoPathFor("B")].StatementId.Value;
        var receipt = new DigestionCoverageReceipt(
            receiptGid,
            atom.Fingerprints.RawSha256,
            receiptStatementId ?? oldTarget);
        var entry = Entry(
            atom,
            "mathlib-reanchor-receipt",
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            [receiptGid],
            new DigestionReceipts([receipt], [], [], [], null),
            includeBoundary: true);
        var document = Document(AtomizerRegistry.NoAtomizerId, [entry]);
        var baseFiles = DigestionReanchorInputFiles(
            baseModules,
            [baseAEvent, baseBEvent],
            sourceBytes,
            atom,
            upgraded: false);
        var candidateFiles = DigestionReanchorInputFiles(
            candidateModules,
            [candidateAEvent, baseBEvent],
            sourceBytes,
            atom,
            upgraded: pinsChanged);
        var protectedBase = RepositorySnapshot.Create(
            baseFiles.ToImmutableDictionary(static file => file.Path));
        var candidate = RepositorySnapshot.Create(
            candidateFiles.ToImmutableDictionary(static file => file.Path));
        var report = DigestionReanchorReport(candidateModules);
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(candidate, report)).Capability;
        var changes = RawChangeSet.CreateWithKinds(
        [
            (baseAEvent.Path.Value, RawChangeKind.Deleted),
            (candidateAEvent.Path.Value, RawChangeKind.Added),
            (PathFor("A"), RawChangeKind.Modified),
            .. pinsChanged
                ? new[]
                {
                    ("lean-toolchain", RawChangeKind.Modified),
                    ("lake-manifest.json", RawChangeKind.Modified),
                }
                : Array.Empty<(string, RawChangeKind)>(),
        ]);
        return new DigestionReanchorFixture(
            protectedBase,
            candidate,
            changes,
            lean,
            document,
            candidateCatalog.ByPath[RepoPathFor("A")].StatementId.Value);
    }

    private static ImmutableArray<RepositoryFile> DigestionReanchorInputFiles(
        IReadOnlyList<ModuleSpec> modules,
        ImmutableArray<RepositoryFile> events,
        byte[] sourceBytes,
        DigestionAtom atom,
        bool upgraded)
    {
        var files = modules.Select(module => DigestionReanchorTextFile(
                PathFor(module.Name),
                module.Source))
            .Append(DigestionReanchorTextFile(
                "lean-toolchain",
                upgraded
                    ? "leanprover/lean4:v4.25.0\n"
                    : "leanprover/lean4:v4.24.0\n"))
            .Append(DigestionReanchorTextFile(
                "lake-manifest.json",
                DigestionReanchorMathlibManifest(
                    upgraded ? new string('b', 40) : new string('a', 40))))
            .Append(new RepositoryFile(
                RepoPath.CreateKnown("docs/source.md"),
                ImmutableArray.CreateRange(sourceBytes),
                Encoding.UTF8.GetString(sourceBytes)))
            .Append(new RepositoryFile(
                RepoPath.CreateKnown(CasFile(atom).Path),
                ImmutableArray.CreateRange(CasFile(atom).Bytes),
                Encoding.UTF8.GetString(CasFile(atom).Bytes)))
            .Concat(events)
            .ToImmutableArray();
        return files;
    }

    private static LeanAxiomReport DigestionReanchorReport(IReadOnlyList<ModuleSpec> modules) =>
        LeanAxiomReport.Create(modules.ToDictionary(
            module => PathFor(module.Name),
            module => new LeanFileReport(
                module.Imports.Select(imported => $"D5.S0.Carrier.{imported}").ToImmutableArray(),
                [new LeanDeclaration(
                    module.Name.ToLowerInvariant(),
                    module.Kind,
                    module.StatementMaterial,
                    module.Axioms)
                {
                    NameKey = $"ns(n0,1:{module.Name.ToLowerInvariant()})",
                }]),
            StringComparer.Ordinal));

    private static RepositoryFile DigestionReanchorLedgerEventFor(
        ImmutableArray<RepositoryFile> events,
        string module) =>
        events.Single(file => FrozenLedgerBaseViewReader.Read(
                RepositorySnapshot.Create(ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(
                    file.Path,
                    file)))
            .ActiveByPath.ContainsKey(RepoPathFor(module)));

    private static RepositoryFile DigestionReanchorTextFile(string path, string text) => new(
        RepoPath.CreateKnown(path),
        ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text)),
        text);

    private static Dictionary<string, string> DigestionReanchorTextDictionary(
        RepositorySnapshot snapshot) =>
        snapshot.Files.ToDictionary(
            static item => item.Key.Value,
            static item => item.Value.Text,
            StringComparer.Ordinal);

    private static RawRepositorySnapshot DigestionReanchorRawSnapshot(
        IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));

    private static string DigestionReanchorMathlibManifest(string revision) =>
        JsonSerializer.Serialize(new
        {
            packages = new[]
            {
                new
                {
                    name = "mathlib",
                    type = "git",
                    url = "https://github.com/leanprover-community/mathlib4",
                    rev = revision,
                },
            },
        }) + "\n";

    private static DigestionLedgerEvaluation EvaluateDigestionReanchorFixture(
        DigestionReanchorFixture fixture,
        BackfillInventoryDocument document) =>
        DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            fixture.Candidate,
            fixture.Lean,
            baselineDocument: fixture.Document,
            changes: fixture.Changes);

    private static void AssertRejectedDigestionReanchorRemainsFatal(
        DigestionReanchorFixture fixture)
    {
        var before = BackfillInventoryWriter.WriteAtom(
            Assert.Single(fixture.Document.RequireDigestionEntries()));

        var reanchored = MathlibUpgradeDigestionReanchor.Apply(
            fixture.Document,
            fixture.ProtectedBase,
            fixture.Candidate,
            fixture.Changes,
            fixture.Lean);

        Assert.Equal(
            before.ToArray(),
            BackfillInventoryWriter.WriteAtom(
                Assert.Single(reanchored.RequireDigestionEntries())).ToArray());
        AssertCoverageReceiptMismatchIsFatal(fixture, reanchored);
    }

    private static void AssertCoverageReceiptMismatchIsFatal(
        DigestionReanchorFixture fixture,
        BackfillInventoryDocument document)
    {
        var gap = Assert.Single(
            EvaluateDigestionReanchorFixture(fixture, document).Entries.Single().Gaps,
            static item => item.Code == "coverage-receipt-mismatch");
        Assert.Equal(DigestionGapSeverity.ReceiptIntegrityFailure, gap.Severity);
    }

    private sealed record DigestionReanchorFixture(
        RepositorySnapshot ProtectedBase,
        RepositorySnapshot Candidate,
        RawChangeSet Changes,
        AcceptedLeanClosure Lean,
        BackfillInventoryDocument Document,
        string CandidateAStatementId);
}
