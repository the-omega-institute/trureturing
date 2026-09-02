using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FormalizationReceiptIdentityTests
{
    private const int RuleNumber = 31;
    private const string BareAtomId =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string OtherBareAtomId =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    private const string CanonicalPath =
        "Meta/Digestion/formalizations/" + BareAtomId + ".v1.json";
    private const string LegacyAtomId = "generic-residual-" + BareAtomId;
    private const string LegacyPath =
        "Meta/Digestion/formalizations/" + LegacyAtomId + ".v1.json";
    private const string PrimaryGid = "D5/S0/Carrier/Ring.goldenRing";
    private const string OtherPrimaryGid = "D5/S0/Carrier/ValuesBinding.fixtureValue";
    private const string HostedGid = "D5/S0/Carrier/Ring.hosted";
    private const string ReplacementHostedGid = "D5/S0/Carrier/Ring.replacement";
    private const string PrimaryNameKey =
        "ns(ns(ns(ns(ns(n0,2:D5),2:S0),7:Carrier),4:Ring),10:goldenRing)";
    private const string HostedNameKey =
        "ns(ns(ns(ns(ns(n0,2:D5),2:S0),7:Carrier),4:Ring),6:hosted)";
    private const string UnrelatedPath = "notes/unrelated.txt";
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";
    private const string Sha256Prefix = "sha256:";

    [Fact]
    public void LegacyNamedHistoricalReceiptIsRejected()
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, LegacyPath, ReceiptText(Receipt(LegacyAtomId)));

        Assert.Equal(1, CountFindings(Execute(fixture, LegacyPath)));
    }

    [Fact]
    public void ChangedReceiptAtomIdIsRejectedByTransitionClause()
    {
        var fixture = Transition(Receipt(atomId: OtherBareAtomId), Receipt());

        AssertRejected(fixture, "unchanged atom_id");
    }

    [Fact]
    public void NewReceiptIsOutsideTheTransitionRule()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = ReceiptText(Receipt());

        Assert.Empty(Findings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void TypeOnlySignatureReanchorMatchingReportAndEquivalentSourceIsAdmitted()
    {
        var fixture = Transition(
            Receipt(signature: Signature(type: "OldNat")),
            Receipt(signature: Signature(type: "Nat")));
        AddFrozenRing(fixture, Signature(type: "Nat"));
        AssertEquivalentSourceFixture(fixture);

        Assert.Empty(Findings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void HostedExtensionAppendMatchingReportIsAdmitted()
    {
        var extension = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var fixture = Transition(Receipt(), Receipt(hosted: [extension]));
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            Signature(),
            extension.Signature);

        Assert.Empty(Findings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void ChangedSignatureNameKeyIsRejectedByNamedClause()
    {
        var fixture = Transition(
            Receipt(),
            Receipt(signature: Signature(nameKey: "renamed")));

        AssertRejected(fixture, "name_key");
    }

    [Fact]
    public void ChangedSignatureKindIsRejectedByNamedClause()
    {
        var fixture = Transition(
            Receipt(),
            Receipt(signature: Signature(kind: "theorem")));

        AssertRejected(fixture, "kind");
    }

    [Fact]
    public void ChangedCasRefIsRejectedByNamedClause()
    {
        var fixture = Transition(
            Receipt(),
            Receipt(casRef: Fingerprint('b')));

        AssertRejected(fixture, "cas_ref");
    }

    [Fact]
    public void ChangedRawSha256IsRejectedByNamedClause()
    {
        var fixture = Transition(
            Receipt(),
            Receipt(rawSha256: Fingerprint('b')));

        AssertRejected(fixture, "raw_sha256");
    }

    [Fact]
    public void ChangedPrimaryGidIsRejectedByNamedClause()
    {
        var fixture = Transition(
            Receipt(),
            Receipt(primaryGid: OtherPrimaryGid));

        AssertRejected(fixture, "primary_gid");
    }

    [Fact]
    public void ChangedSchemaIsRejectedByNamedClause()
    {
        var fixture = Transition(Receipt(), Receipt());
        fixture.Files[CanonicalPath] = fixture.Files[CanonicalPath].Replace(
            DigestionFormalizationReceipt.Schema,
            "digestion-formalization-v2",
            StringComparison.Ordinal);

        AssertRejected(fixture, "schema");
    }

    [Fact]
    public void ReanchoredTypeMustEqualCandidateReport()
    {
        var fixture = Transition(
            Receipt(signature: Signature(type: "OldNat")),
            Receipt(signature: Signature(type: "WrongNat")));
        AddFrozenRing(fixture, Signature(type: "Nat"));

        AssertRejected(fixture, "candidate report");
    }

    [Fact]
    public void ReanchoredCandidateReportNameKeyMustMatchCompletely()
    {
        var fixture = Transition(
            Receipt(signature: Signature(type: "OldNat")),
            Receipt(signature: Signature(type: "Nat")));
        AddFrozenRing(fixture, Signature(type: "Nat"));
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            Signature(nameKey: "ns(n0,7:renamed)", type: "Nat"));

        AssertRejected(fixture, "complete (name_key, kind, type)");
    }

    [Fact]
    public void ReanchoredCandidateReportKindMustMatchCompletely()
    {
        var fixture = Transition(
            Receipt(signature: Signature(type: "OldNat")),
            Receipt(signature: Signature(type: "Nat")));
        AddFrozenRing(fixture, Signature(type: "Nat"));
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            Signature(kind: "theorem", type: "Nat"));

        AssertRejected(fixture, "complete (name_key, kind, type)");
    }

    [Fact]
    public void ReanchoredTypeWithChangedPropositionSourceIsRejected()
    {
        var fixture = Transition(
            Receipt(signature: Signature(type: "Nat")),
            Receipt(signature: Signature(type: "Int")));
        AddFrozenRing(fixture, Signature(type: "Nat"));
        var baselineSource = fixture.Baseline[RuleFixture.RingPath];
        fixture.Files[RuleFixture.RingPath] = baselineSource.Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Int := 0",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = RingReport(Signature(type: "Int"));

        AssertRejected(
            fixture,
            "equivalent Lean proposition source",
            CanonicalPath,
            RuleFixture.RingPath);
    }

    [Fact]
    public void ExistingHostedExtensionDeletionIsRejectedWithMigrationClause()
    {
        var extension = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var fixture = Transition(
            Receipt(hosted: [extension]),
            Receipt());

        AssertRejected(fixture, "removed or replaced");
    }

    [Fact]
    public void ExistingHostedExtensionReplacementIsRejectedWithMigrationClause()
    {
        var existing = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var replacement = Extension(
            ReplacementHostedGid,
            Signature("replacement", "theorem", "True"));
        var fixture = Transition(
            Receipt(hosted: [existing]),
            Receipt(hosted: [replacement]));

        AssertRejected(fixture, "removed or replaced");
    }

    [Fact]
    public void DuplicateHostedExtensionGidIsRejectedByNamedClause()
    {
        var extension = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var fixture = new RuleFixture();
        fixture.Reports[RuleFixture.RingPath] = RingReport(Signature(), extension.Signature);
        var context = fixture.Build(RawChangeSet.Create([CanonicalPath]));
        var result = DigestionFormalizationReceiptTransition.Evaluate(
            Receipt(),
            Receipt(hosted: [extension, extension]),
            context.Baseline,
            context.Current,
            context.Lean.Report);

        Assert.Equal(DigestionFormalizationReceiptTransitionKind.Rejected, result.Kind);
        Assert.Contains("every hosted GID to be unique", result.Clause, StringComparison.Ordinal);
    }

    [Fact]
    public void HostedAppendMixedWithPrimaryTypeReanchorIsRejected()
    {
        var extension = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var fixture = Transition(
            Receipt(signature: Signature(type: "OldNat")),
            Receipt(signature: Signature(type: "Nat"), hosted: [extension]));
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            Signature(),
            extension.Signature);

        AssertRejected(fixture, "mixed transition");
    }

    [Fact]
    public void ProtectedBaselineNotForkPointOwnsTheOldReceiptAndSource()
    {
        var baselineReceipt = Receipt(signature: Signature(type: "OldNat"));
        var candidateReceipt = Receipt(signature: Signature(type: "Nat"));
        var fixture = Transition(baselineReceipt, candidateReceipt);
        AddFrozenRing(fixture, Signature(type: "Nat"));
        fixture.ForkPoint[CanonicalPath] = ReceiptText(
            baselineReceipt with { CasRef = Fingerprint('b') });
        fixture.ForkPoint[RuleFixture.RingPath] = fixture.ForkPoint[RuleFixture.RingPath].Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Bool := false",
            StringComparison.Ordinal);
        AssertEquivalentSourceFixture(fixture);

        Assert.Empty(Findings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void LeanChangeWithoutReceiptDeltaDoesNotReverseScanReceipts()
    {
        var fixture = new RuleFixture();
        SetHistorical(
            fixture,
            CanonicalPath,
            ReceiptText(Receipt(signature: Signature(type: "OldNat"))));
        fixture.Reports[RuleFixture.RingPath] = RingReport(Signature(type: "Nat"));

        Assert.Equal(
            0,
            CountFindings(Execute(fixture, RuleFixture.RingPath)));
    }

    [Fact]
    [BaseFactScopeProbe(31)]
    public void Sl031FormalizationReceiptIdentityScopesHistoryAndKeepsOnlyReceiptDeltaChecks()
    {
        var unrelated = new RuleFixture();
        SetHistorical(
            unrelated,
            CanonicalPath,
            ReceiptText(Receipt(atomId: OtherBareAtomId)));
        unrelated.Files[UnrelatedPath] = "candidate\n";
        Assert.Equal(0, CountFindings(Execute(unrelated, UnrelatedPath)));

        var changed = Transition(Receipt(), Receipt(atomId: OtherBareAtomId));
        Assert.Equal(1, CountFindings(Execute(changed, CanonicalPath)));

        var implementation = new RuleFixture();
        SetHistorical(
            implementation,
            CanonicalPath,
            ReceiptText(Receipt(atomId: OtherBareAtomId)));
        Assert.Equal(0, CountFindings(Execute(implementation, RuleImplementationPath)));
    }

    private static RuleFixture Transition(
        DigestionFormalizationReceipt baseline,
        DigestionFormalizationReceipt candidate)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, CanonicalPath, ReceiptText(baseline));
        fixture.Files[CanonicalPath] = ReceiptText(candidate);
        return fixture;
    }

    private static void SetHistorical(
        RuleFixture fixture,
        string path,
        string contents)
    {
        fixture.Baseline[path] = contents;
        fixture.ForkPoint[path] = contents;
        fixture.Files[path] = contents;
    }

    private static void AddFrozenRing(
        RuleFixture fixture,
        DigestionFormalizationSignature baselineSignature)
    {
        const string valuesBindingSource = "def fixtureValue : Int := 0\n";
        fixture.Baseline[RuleFixture.ValuesBindingPath] = valuesBindingSource;
        fixture.ForkPoint[RuleFixture.ValuesBindingPath] = valuesBindingSource;
        fixture.Files[RuleFixture.ValuesBindingPath] = valuesBindingSource;

        var path = RepoPath.CreateKnown(RuleFixture.RingPath);
        var source = $"def goldenRing : {baselineSignature.Type} := 0\n";
        fixture.Baseline[RuleFixture.RingPath] = source;
        fixture.ForkPoint[RuleFixture.RingPath] = source;
        fixture.Files[RuleFixture.RingPath] = source;
        var report = RingReport(baselineSignature);
        fixture.BaselineReports[RuleFixture.RingPath] = report;
        fixture.Reports[RuleFixture.RingPath] = report;
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(path, report);
        var statementId = StatementId.Create(Fingerprint('d'));
        var material = new FrozenNodeMaterial(
            path,
            declarations,
            statementId,
            FrozenContentAddress.ComputeFrozenNodeId(path, statementId, []),
            [],
            []);
        var catalog = FrozenMaterialCatalog.Create(
            ImmutableDictionary<RepoPath, TruthState>.Empty.Add(path, TruthState.Closed),
            [material],
            ImmutableDictionary<RepoPath, ImmutableArray<CaseId>>.Empty,
            ImmutableDictionary<RepoPath, ImmutableArray<string>>.Empty);
        foreach (var file in FrozenLedgerTestData.EventFiles(catalog))
        {
            var text = Encoding.UTF8.GetString(file.RawBytes.AsSpan());
            fixture.Baseline[file.Path.Value] = text;
            fixture.ForkPoint[file.Path.Value] = text;
            fixture.Files[file.Path.Value] = text;
        }
    }

    private static void AssertEquivalentSourceFixture(RuleFixture fixture)
    {
        var context = fixture.Build(RawChangeSet.Create([CanonicalPath]));
        var path = RepoPath.CreateKnown(RuleFixture.RingPath);
        var baseView = FrozenLedgerBaseViewReader.Read(context.Baseline);
        var states = LeanTruthStates.Resolve(context.Current, context.Lean);
        var adjacency = LeanImportAdjacency.Build(context.Current, context.Lean);
        var candidateCatalog = FrozenContentAddress.BuildAdmissionCatalog(
            context.Current,
            context.Lean,
            states,
            adjacency,
            ImmutableHashSet.Create(path),
            baseView.ActiveByPath);
        var baseSource = LeanSourceCatalog.Parse(context.Baseline).ExtractPropositionSource(
            path,
            baseView.ActiveByPath[path].Material.DeclarationStatementIds);
        var candidateSource = LeanSourceCatalog.Parse(context.Current).ExtractPropositionSource(
            path,
            candidateCatalog.ByPath[path].DeclarationStatementIds);

        Assert.Equal(
            Encoding.UTF8.GetString(baseSource.AsSpan()),
            Encoding.UTF8.GetString(candidateSource.AsSpan()));
    }

    private static LeanFileReport RingReport(
        DigestionFormalizationSignature primary,
        DigestionFormalizationSignature? hosted = null)
    {
        var declarations = ImmutableArray.CreateBuilder<LeanDeclaration>();
        declarations.Add(Declaration("goldenRing", primary));
        if (hosted is not null)
        {
            declarations.Add(Declaration("hosted", hosted));
        }

        return new LeanFileReport([], declarations.ToImmutable());
    }

    private static LeanDeclaration Declaration(
        string name,
        DigestionFormalizationSignature signature) =>
        new(name, signature.Kind, signature.Type, [])
        {
            NameKey = signature.NameKey,
        };

    private static DigestionFormalizationReceipt Receipt(
        string? atomId = null,
        string? primaryGid = null,
        DigestionFormalizationSignature? signature = null,
        string? casRef = null,
        string? rawSha256 = null,
        ImmutableArray<DigestionFormalizationExtension> hosted = default) =>
        new(
            atomId ?? BareAtomId,
            primaryGid ?? PrimaryGid,
            signature ?? Signature(),
            casRef ?? Fingerprint('a'),
            rawSha256 ?? Fingerprint('a'),
            hosted);

    private static DigestionFormalizationSignature Signature(
        string nameKey = PrimaryNameKey,
        string kind = "def",
        string type = "Nat") =>
        new(nameKey, kind, type);

    private static DigestionFormalizationExtension Extension(
        string gid,
        DigestionFormalizationSignature signature) =>
        new(gid, signature);

    private static string ReceiptText(DigestionFormalizationReceipt receipt) =>
        Encoding.UTF8.GetString(DigestionFormalizationReceipt.Write(receipt).AsSpan());

    private static string Fingerprint(char digit) =>
        Sha256Prefix + new string(digit, 64);

    private static void AssertRejected(
        RuleFixture fixture,
        string clause,
        params string[] changedPaths)
    {
        var completed = Execute(
            fixture,
            changedPaths.Length == 0 ? [CanonicalPath] : changedPaths);
        var finding = Assert.Single(completed.Diagnostics.Where(diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(RuleNumber)));
        Assert.Contains(clause, finding.Message, StringComparison.Ordinal);
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, params string[] changedPaths)
    {
        var outcome = RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create(changedPaths)));
        if (outcome is RuleExecutionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail("INFRA: " + failure.Message);
        }

        return Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
    }

    private static int CountFindings(CompletedRuleSet completed) =>
        Findings(completed).Length;

    private static ImmutableArray<Diagnostic> Findings(CompletedRuleSet completed) =>
        completed.Diagnostics.Where(diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(RuleNumber)).ToImmutableArray();
}
