using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenSurfaceRuleTests
{
    private const string FrozenPath = RuleFixture.RingPath;
    private const string OtherPath = RuleFixture.BlueprintPath;
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
    public void Sl008AllowsSnapshotReplacementOfAcceptedEventFragment(RawChangeKind kind)
    {
        var fixture = FrozenFixture(out var eventPath);
        if (kind == RawChangeKind.Deleted)
        {
            fixture.Files.Remove(eventPath);
        }

        var evaluation = Evaluate(fixture, (eventPath, kind));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008AllowsAddedAcceptedEventFragment()
    {
        var fixture = FrozenFixture(out var eventPath);

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008IgnoresModifiedNonFrozenModule()
    {
        var fixture = FrozenFixture(out _);

        var evaluation = Evaluate(fixture, (OtherPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    private static RuleFixture FrozenFixture(out string eventPath)
    {
        var fixture = new RuleFixture();
        eventPath = AddFreeze(fixture, FrozenPath);
        return fixture;
    }

    private static string AddFreeze(
        RuleFixture fixture,
        string descriptorSelector)
    {
        var path = RepoPath.CreateKnown(descriptorSelector);
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(
            path,
            fixture.Reports[descriptorSelector]);
        var material = new FrozenNodeMaterial(
            path,
            declarations,
            StatementId.Create(FrozenContentHash.Compute(
                FrozenHashDomains.Statement,
                CanonicalStatementWriter.WriteModule(path, declarations).AsSpan())),
            FrozenNodeId.Create("sha256:" + new string('0', 64)),
            [],
            []);
        var payload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(material));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash);
        fixture.Files[eventPath] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return eventPath;
    }

    private static SingleRuleEvaluation Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(changes)));

}
