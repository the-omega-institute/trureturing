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
    private const string OtherCanonicalPath =
        "Meta/Digestion/formalizations/" + OtherBareAtomId + ".v1.json";
    private const string LegacyAtomId = "generic-residual-" + BareAtomId;
    private const string LegacyPath =
        "Meta/Digestion/formalizations/" + LegacyAtomId + ".v1.json";
    private const string PrimaryGid = "D5/S0/Carrier/Ring.goldenRing";
    private const string OtherPrimaryGid = "D5/S0/Carrier/ValuesBinding.fixtureValue";
    private const string HostedGid = "D5/S0/Carrier/Ring.hosted";
    private const string ReplacementHostedGid = "D5/S0/Carrier/Ring.replacement";
    private const string OtherGid = "D5/S0/Carrier/Other.other";
    private const string OtherPath = "D5/S0/Carrier/Other.lean";
    private const string PrimaryNameKey =
        "ns(ns(ns(ns(ns(n0,2:D5),2:S0),7:Carrier),4:Ring),10:goldenRing)";
    private const string HostedNameKey =
        "ns(ns(ns(ns(ns(n0,2:D5),2:S0),7:Carrier),4:Ring),6:hosted)";
    private const string OtherNameKey =
        "ns(ns(ns(ns(ns(n0,2:D5),2:S0),7:Carrier),5:Other),5:other)";
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
    public void NewReceiptKeepsFilenameIdentityLawButIsOutsideTransitionEvaluation()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = ReceiptText(Receipt(atomId: OtherBareAtomId));

        var finding = Assert.Single(Findings(Execute(fixture, CanonicalPath)));
        Assert.Contains("atom_id must match filename", finding.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("transition Rejected", finding.Message, StringComparison.Ordinal);
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

    [Theory]
    [InlineData("name_key")]
    [InlineData("kind")]
    [InlineData("type")]
    public void HostedAppendSignatureMustEqualCandidateReportCompletely(string field)
    {
        var candidateSignature = field switch
        {
            "name_key" => Signature("renamed-hosted", "theorem", "True"),
            "kind" => Signature(HostedNameKey, "def", "True"),
            _ => Signature(HostedNameKey, "theorem", "False"),
        };
        var candidate = Extension(HostedGid, candidateSignature);
        var report = Signature(HostedNameKey, "theorem", "True");
        var fixture = Transition(Receipt(), Receipt(hosted: [candidate]));
        fixture.Reports[RuleFixture.RingPath] = RingReport(Signature(), report);

        AssertRejected(fixture, "complete (name_key, kind, type)");
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

    [Theory]
    [InlineData("name_key")]
    [InlineData("kind")]
    public void ExistingHostedSignatureNameKeyAndKindCannotChange(string field)
    {
        var baseline = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var candidateSignature = field == "name_key"
            ? Signature("renamed-hosted", "theorem", "True")
            : Signature(HostedNameKey, "def", "True");
        var candidate = Extension(HostedGid, candidateSignature);
        var fixture = Transition(
            Receipt(hosted: [baseline]),
            Receipt(hosted: [candidate]));

        AssertRejected(fixture, field);
    }

    [Fact]
    public void ReanchoredHostedSignatureMustEqualCandidateReportCompletely()
    {
        var baseline = Extension(HostedGid, Signature(HostedNameKey, "theorem", "Old.True"));
        var candidate = Extension(HostedGid, Signature(HostedNameKey, "theorem", "True"));
        var fixture = Transition(
            Receipt(hosted: [baseline]),
            Receipt(hosted: [candidate]));
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            Signature(),
            Signature(HostedNameKey, "theorem", "False"));

        AssertRejected(fixture, "complete (name_key, kind, type)");
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
    public void DeletedReceiptIsOutsideTheTransitionRule()
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, CanonicalPath, ReceiptText(Receipt()));
        fixture.Files.Remove(CanonicalPath);

        Assert.Empty(Findings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void BatchSourceComparisonRejectsOnlyReceiptWhoseModuleChanged()
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, RuleFixture.RingPath, "def goldenRing : Nat := 0\n");
        SetHistorical(fixture, RuleFixture.ValuesBindingPath, "def fixtureValue : Int := 0\n");
        SetHistorical(
            fixture,
            CanonicalPath,
            ReceiptText(Receipt(signature: Signature(type: "Nat"))));
        fixture.Files[CanonicalPath] = ReceiptText(Receipt(signature: Signature(type: "Int")));
        SetHistorical(
            fixture,
            OtherCanonicalPath,
            ReceiptText(Receipt(
                atomId: OtherBareAtomId,
                primaryGid: OtherGid,
                signature: Signature(OtherNameKey, "def", "OldNat"))));
        fixture.Files[OtherCanonicalPath] = ReceiptText(Receipt(
            atomId: OtherBareAtomId,
            primaryGid: OtherGid,
            signature: Signature(OtherNameKey, "def", "Nat")));
        const string otherSource = "def other : Nat := 1\n";
        SetHistorical(fixture, OtherPath, otherSource);
        AddFrozenDeclarations(
            fixture,
            (RuleFixture.RingPath, "goldenRing", Signature(type: "Nat"), 'd'),
            (OtherPath, "other", Signature(OtherNameKey, "def", "Nat"), 'e'));
        fixture.Files[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath].Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Int := 0",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = FileReport(
            "goldenRing",
            Signature(type: "Int"));

        var findings = Findings(Execute(
            fixture,
            CanonicalPath,
            OtherCanonicalPath,
            RuleFixture.RingPath));

        var finding = Assert.Single(findings);
        Assert.Equal(CanonicalPath, finding.Path);
        Assert.DoesNotContain(findings, item => item.Path == OtherCanonicalPath);
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

        var source = $"def goldenRing : {baselineSignature.Type} := 0\n";
        fixture.Baseline[RuleFixture.RingPath] = source;
        fixture.ForkPoint[RuleFixture.RingPath] = source;
        fixture.Files[RuleFixture.RingPath] = source;
        AddFrozenDeclarations(
            fixture,
            (RuleFixture.RingPath, "goldenRing", baselineSignature, 'd'));
    }

    private static void AddFrozenDeclarations(
        RuleFixture fixture,
        params (string Path, string Declaration, DigestionFormalizationSignature Signature, char StatementDigit)[]
            declarations)
    {
        var states = ImmutableDictionary.CreateBuilder<RepoPath, TruthState>();
        var materials = ImmutableArray.CreateBuilder<FrozenNodeMaterial>();
        foreach (var declaration in declarations)
        {
            var path = RepoPath.CreateKnown(declaration.Path);
            var report = FileReport(declaration.Declaration, declaration.Signature);
            fixture.BaselineReports[declaration.Path] = report;
            fixture.Reports[declaration.Path] = report;
            var statementIds = CanonicalStatementWriter.DeclarationStatementIds(path, report);
            var statementId = StatementId.Create(Fingerprint(declaration.StatementDigit));
            states.Add(path, TruthState.Closed);
            materials.Add(new FrozenNodeMaterial(
                path,
                statementIds,
                statementId,
                FrozenContentAddress.ComputeFrozenNodeId(path, statementId, []),
                [],
                []));
        }

        var catalog = FrozenMaterialCatalog.Create(
            states.ToImmutable(),
            materials.ToImmutable(),
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

    private static LeanFileReport FileReport(
        string declaration,
        DigestionFormalizationSignature signature) =>
        new([], [Declaration(declaration, signature)]);

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
