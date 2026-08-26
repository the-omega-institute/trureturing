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
        Assert.Contains("ledger-append", diagnostic.Message, StringComparison.Ordinal);
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
    public void Sl008IgnoresModifiedNonFrozenModule()
    {
        var fixture = FrozenFixture();

        var evaluation = Evaluate(fixture, (OtherPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    private static RuleFixture FrozenFixture()
    {
        var fixture = new RuleFixture();
        _ = AddFreeze(fixture, FrozenNodeId, FrozenPath);
        return fixture;
    }

    private static string AddFreeze(
        RuleFixture fixture,
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
            supporting_blob_oids = Array.Empty<string>(),
        };
        var payload = JsonSerializer.SerializeToElement(new
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
        });
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);
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
