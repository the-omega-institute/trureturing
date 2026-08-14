using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenSurfaceRuleTests
{
    private const string FrozenPath = RuleFixture.RingPath;
    private const string OtherPath = RuleFixture.BlueprintPath;
    private const string FrozenNodeId =
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string ReattestedNodeId =
        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    [Theory]
    [InlineData(RawChangeKind.Modified)]
    [InlineData(RawChangeKind.Deleted)]
    public void Sl008RejectsChangedHearts(RawChangeKind kind)
    {
        var fixture = new RuleFixture();
        if (kind == RawChangeKind.Deleted)
        {
            fixture.Files.Remove(RuleFixture.HeartsPath);
            fixture.Reports.Remove(RuleFixture.HeartsPath);
        }

        var evaluation = Evaluate(fixture, (RuleFixture.HeartsPath, kind));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(RuleFixture.HeartsPath, diagnostic.Path);
        Assert.Contains("SL-022", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsUnchangedHearts()
    {
        var fixture = new RuleFixture();

        var evaluation = Evaluate(fixture);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Theory]
    [InlineData(RawChangeKind.Modified)]
    [InlineData(RawChangeKind.Deleted)]
    public void Sl008RejectsChangedAcceptedEventFragment(RawChangeKind kind)
    {
        var fixture = FrozenFixture();
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(FrozenNodeId);
        if (kind == RawChangeKind.Deleted)
        {
            fixture.Files.Remove(eventPath);
        }

        var evaluation = Evaluate(fixture, (eventPath, kind));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains("ledger-reattest", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("already-frozen fragment", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsAddedAcceptedEventFragment()
    {
        var fixture = FrozenFixture();
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(FrozenNodeId);

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsModifiedFrozenModuleWithoutAddedReattest()
    {
        var fixture = FrozenFixture();

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Contains("ledger-reattest", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("already-frozen module", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008KeepsChangedFileGuardWhenEnvironmentPinsAreUnchanged()
    {
        var fixture = FrozenFixture();

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Contains("already-frozen module", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("ledger-reattest", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("lean-toolchain")]
    [InlineData("lakefile.toml")]
    [InlineData("lakefile.lean")]
    [InlineData("lake-manifest.json")]
    public void Sl008RejectsAmbientDriftInUnchangedFrozenModuleWhenEnvironmentPinChanges(
        string environmentPin)
    {
        var fixture = FrozenFixture();
        DriftFrozenStatementIdentity(fixture);
        fixture.Baseline[environmentPin] = "baseline pin\n";
        fixture.Files[environmentPin] = "candidate pin\n";

        var evaluation = Evaluate(fixture, (environmentPin, RawChangeKind.Modified));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("1 declaration statement identity drift", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008KeepsChangedFileScopeForAmbientDriftWhenEnvironmentPinsAreUnchanged()
    {
        var fixture = FrozenFixture();
        DriftFrozenStatementIdentity(fixture);

        var evaluation = Evaluate(fixture);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008AllowsAmbientDriftWithMatchingAddedEnvironmentRecoordinate()
    {
        var (fixture, oldState, freezeEventHash) = EnvironmentRecoordinateFixture();
        DriftFrozenStatementIdentity(fixture);
        ChangeEnvironmentPin(fixture);
        var recoordinatePath = AddEnvironmentRecoordinate(
            fixture,
            oldState,
            fixture.Reports[FrozenPath],
            freezeEventHash);

        var evaluation = Evaluate(
            fixture,
            ("lean-toolchain", RawChangeKind.Modified),
            (recoordinatePath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsAmbientDriftWhenAddedEnvironmentRecoordinateHasDifferentNewIdentity()
    {
        var (fixture, oldState, freezeEventHash) = EnvironmentRecoordinateFixture();
        DriftFrozenStatementIdentity(fixture);
        ChangeEnvironmentPin(fixture);
        var recoordinatePath = AddEnvironmentRecoordinate(
            fixture,
            oldState,
            ReportWithStatement("Bool"),
            freezeEventHash);

        var evaluation = Evaluate(
            fixture,
            ("lean-toolchain", RawChangeKind.Modified),
            (recoordinatePath, RawChangeKind.Added));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Contains("1 declaration statement identity drift", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RejectsNewAmbientDriftWhenEnvironmentRecoordinateAlreadyExists()
    {
        var (fixture, oldState, freezeEventHash) = EnvironmentRecoordinateFixture();
        var recoordinatePath = AddEnvironmentRecoordinate(
            fixture,
            oldState,
            ReportWithStatement("Int"),
            freezeEventHash);
        fixture.Baseline[recoordinatePath] = fixture.Files[recoordinatePath];
        fixture.Reports[FrozenPath] = ReportWithStatement("Bool");
        ChangeEnvironmentPin(fixture);

        var evaluation = Evaluate(fixture, ("lean-toolchain", RawChangeKind.Modified));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Contains("1 declaration statement identity drift", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsModifiedFrozenModuleWithMatchingAddedReattest()
    {
        var fixture = FrozenFixture();
        var reattestPath = AddEvent(fixture, "Reattest", ReattestedNodeId, FrozenPath);

        var evaluation = Evaluate(
            fixture,
            (FrozenPath, RawChangeKind.Modified),
            (reattestPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsIncompleteAddedReattestPayload()
    {
        var fixture = FrozenFixture();
        var reattestPath = AddIncompleteReattest(fixture, ReattestedNodeId, FrozenPath);

        var evaluation = Evaluate(
            fixture,
            (FrozenPath, RawChangeKind.Modified),
            (reattestPath, RawChangeKind.Added));

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == FrozenLedgerChangeClassifier.AcceptedRoot
            && diagnostic.Message.Contains("candidate frozen ledger is invalid", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl008DoesNotTreatAnExistingReattestAsAuthorizationForANewModification()
    {
        var fixture = FrozenFixture();
        _ = AddEvent(fixture, "Reattest", ReattestedNodeId, FrozenPath);

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == FrozenPath
            && diagnostic.Message.Contains("ledger-reattest", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl008RejectsDeletedFrozenModuleEvenWithMatchingAddedReattest()
    {
        var fixture = FrozenFixture();
        var reattestPath = AddEvent(fixture, "Reattest", ReattestedNodeId, FrozenPath);
        fixture.Files.Remove(FrozenPath);
        fixture.Reports.Remove(FrozenPath);

        var evaluation = Evaluate(
            fixture,
            (FrozenPath, RawChangeKind.Deleted),
            (reattestPath, RawChangeKind.Added));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(FrozenPath, diagnostic.Path);
        Assert.Contains("deleted", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("already-frozen module", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008IgnoresModifiedNonFrozenModule()
    {
        var fixture = FrozenFixture();

        var evaluation = Evaluate(fixture, (OtherPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    private static RuleFixture FrozenFixture()
    {
        var fixture = new RuleFixture();
        _ = AddEvent(fixture, "Freeze", FrozenNodeId, FrozenPath);
        return fixture;
    }

    private static void DriftFrozenStatementIdentity(RuleFixture fixture) =>
        fixture.Reports[FrozenPath] = ReportWithStatement("Int");

    private static LeanFileReport ReportWithStatement(string type) =>
        new(
            [],
            [new LeanDeclaration("goldenRing", "def", type, [])]);

    private static void ChangeEnvironmentPin(RuleFixture fixture)
    {
        fixture.Baseline["lean-toolchain"] = "baseline pin\n";
        fixture.Files["lean-toolchain"] = "candidate pin\n";
    }

    private static (RuleFixture Fixture, RecoordinateState OldState, string FreezeEventHash)
        EnvironmentRecoordinateFixture()
    {
        var fixture = new RuleFixture();
        var oldState = RecoordinateStateFor(
            fixture.BaselineReports[FrozenPath],
            EnvironmentPins('1'),
            '4',
            '5');
        var payload = new FrozenFreezePayload(
            "active-frozen",
            FrozenLedgerCanonicalWriter.CaseId(oldState.FrozenNodeId),
            oldState.Declarations,
            "admission",
            new FrozenExpectedVerdict(
                ImmutableArray.Create("admit"),
                "none",
                ImmutableArray<FrozenExpectedDiagnostic>.Empty),
            oldState.FrozenNodeId,
            oldState.Input,
            oldState.WitnessId.Value,
            RepoPath.CreateKnown(FrozenPath),
            ImmutableArray<FrozenNodeId>.Empty,
            oldState.FrozenNodeId.Value,
            oldState.StatementId,
            nameof(TruthState.Closed),
            oldState.WitnessId);
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(payload));
        var freezePath = FrozenLedgerChangeClassifier.AcceptedPath(oldState.FrozenNodeId.Value);
        var text = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        fixture.Files[freezePath] = text;
        fixture.Baseline[freezePath] = text;
        return (fixture, oldState, encoded.Hash);
    }

    private static string AddEnvironmentRecoordinate(
        RuleFixture fixture,
        RecoordinateState oldState,
        LeanFileReport newReport,
        string previousAttestationEventHash)
    {
        var newState = RecoordinateStateFor(newReport, EnvironmentPins('2'), '6', '7');
        var payload = new FrozenEnvironmentRecoordinatePayload(
            FrozenLedgerCanonicalWriter.CaseId(oldState.FrozenNodeId),
            newState.Declarations,
            oldState.Declarations,
            newState.Environment,
            oldState.Environment,
            "representation-migration; equivalence-unproved",
            nameof(TruthState.Closed),
            newState.AxiomClosure,
            newState.FrozenNodeId,
            newState.Imports,
            newState.Input,
            ImmutableArray<FrozenNodeId>.Empty,
            newState.StatementId,
            newState.WitnessId,
            oldState.AxiomClosure,
            oldState.FrozenNodeId,
            oldState.Imports,
            oldState.Input,
            ImmutableArray<FrozenNodeId>.Empty,
            oldState.StatementId,
            oldState.WitnessId,
            previousAttestationEventHash,
            "sha256:" + new string('3', 64));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "EnvironmentRecoordinate",
            FrozenLedgerCanonicalWriter.EnvironmentRecoordinateElement(payload));
        var path = FrozenLedgerChangeClassifier.AcceptedPath(newState.FrozenNodeId.Value);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return path;
    }

    private static RecoordinateState RecoordinateStateFor(
        LeanFileReport report,
        FrozenEnvironmentPins environment,
        char commitDigit,
        char treeDigit)
    {
        var path = RepoPath.CreateKnown(FrozenPath);
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(path, report);
        var statementId = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(path, declarations).AsSpan()));
        var imports = report.Imports
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var axiomClosure = report.Declarations
            .SelectMany(static declaration => declaration.Axioms)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var witnessId = FrozenContentAddress.ComputeWitnessId(
            path,
            statementId,
            imports,
            axiomClosure,
            "git-sha1:" + new string('8', 40),
            "sha256:" + new string('3', 64),
            environment.LeanToolchainBlobOid,
            environment.LakeManifestBlobOid);
        var frozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
            path,
            statementId,
            witnessId,
            ImmutableArray<FrozenNodeId>.Empty);
        var supportingBlobOids = new[]
        {
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            environment.LeanToolchainBlobOid,
        }.Order(StringComparer.Ordinal).ToImmutableArray();
        var input = new FrozenLedgerInput(
            "git-sha1:" + new string(commitDigit, 40),
            "git-sha1:" + new string(treeDigit, 40),
            "git-sha1:" + new string('8', 40),
            FrozenPath,
            "repository-snapshot-v1",
            supportingBlobOids);
        return new RecoordinateState(
            declarations,
            environment,
            imports,
            axiomClosure,
            input,
            statementId,
            witnessId,
            frozenNodeId);
    }

    private static FrozenEnvironmentPins EnvironmentPins(char digit) => new(
        "git-sha1:" + new string(digit, 40),
        "git-sha1:" + new string((char)(digit + 2), 40),
        RepoPath.CreateKnown("lakefile.toml"),
        "git-sha1:" + new string((char)(digit + 1), 40));

    private static string AddEvent(
        RuleFixture fixture,
        string eventType,
        string frozenNodeId,
        string descriptorSelector)
    {
        var declarationStatementIds = CanonicalStatementWriter.DeclarationStatementIds(
                RepoPath.CreateKnown(descriptorSelector),
                fixture.Reports[descriptorSelector])
            .Select(static declaration => new
            {
                declaration_name_key = declaration.DeclarationNameKey,
                kind = declaration.Kind,
                statement_id = declaration.StatementId.Value,
            })
            .ToArray();
        var input = new
        {
            base_commit_oid = "git-sha1:" + new string('1', 40),
            base_tree_oid = "git-sha1:" + new string('2', 40),
            descriptor_blob_oid = "git-sha1:" + new string('3', 40),
            descriptor_selector = descriptorSelector,
            materializer = "repository-snapshot-v1",
            supporting_blob_oids = Array.Empty<string>(),
        };
        var payload = eventType switch
        {
            "Freeze" => JsonSerializer.SerializeToElement(new
            {
                case_class = "active-frozen",
                case_id = "delta-v0.1/freeze",
                declaration_statement_ids = declarationStatementIds,
                evaluation = "admission",
                expected = new
                {
                    allowed_dispositions = new[] { "admit" },
                    diagnostic_match = "none",
                    required_diagnostics = Array.Empty<object>(),
                },
                frozen_node_id = frozenNodeId,
                input,
                input_fingerprint = "sha256:" + new string('4', 64),
                node_path = descriptorSelector,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                semantic_receipt = "sha256:" + new string('5', 64),
                statement_id = "sha256:" + new string('6', 64),
                truth_state = "Closed",
                witness_id = "sha256:" + new string('7', 64),
            }),
            "Reattest" => JsonSerializer.SerializeToElement(new
            {
                case_id = "delta-v0.1/reattest",
                declaration_statement_ids = declarationStatementIds,
                frozen_node_id = frozenNodeId,
                input,
                input_fingerprint = "sha256:" + new string('4', 64),
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                previous_attestation_event_hash = "sha256:" + new string('8', 64),
                semantic_receipt = "sha256:" + new string('5', 64),
                statement_id = "sha256:" + new string('6', 64),
                witness_id = "sha256:" + new string('7', 64),
            }),
            _ => throw new ArgumentOutOfRangeException(nameof(eventType)),
        };
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(eventType, payload);
        var path = FrozenLedgerChangeClassifier.AcceptedPath(frozenNodeId);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return path;
    }

    private static string AddIncompleteReattest(
        RuleFixture fixture,
        string frozenNodeId,
        string descriptorSelector)
    {
        var payload = JsonSerializer.SerializeToElement(new
        {
            frozen_node_id = frozenNodeId,
            input = new
            {
                base_commit_oid = "git-sha1:" + new string('1', 40),
                base_tree_oid = "git-sha1:" + new string('2', 40),
                descriptor_blob_oid = "git-sha1:" + new string('3', 40),
                descriptor_selector = descriptorSelector,
                materializer = "repository-snapshot-v1",
                supporting_blob_oids = Array.Empty<string>(),
            },
        });
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Reattest", payload);
        var path = FrozenLedgerChangeClassifier.AcceptedPath(frozenNodeId);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return path;
    }

    private static SingleRuleEvaluation Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(changes)));

    private sealed record RecoordinateState(
        ImmutableArray<FrozenDeclarationStatement> Declarations,
        FrozenEnvironmentPins Environment,
        ImmutableArray<string> Imports,
        ImmutableArray<string> AxiomClosure,
        FrozenLedgerInput Input,
        StatementId StatementId,
        WitnessId WitnessId,
        FrozenNodeId FrozenNodeId);
}
