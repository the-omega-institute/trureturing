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
        fixture.Reports[FrozenPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", "Int", [])]);

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
}
