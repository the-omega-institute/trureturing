using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenSurfaceRuleTests
{
    private const string FrozenPath = RuleFixture.RingPath;
    private const string OtherPath = RuleFixture.BlueprintPath;
    private static readonly string FrozenStatePathValue =
        FrozenStatePath.FromModulePath(RepoPath.CreateKnown(FrozenPath)).Value;
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

    [Fact]
    public void Sl008RejectsStatePinThatDiffersFromTheCurrentReport()
    {
        var fixture = new RuleFixture();
        var actual = ModuleStatementId(fixture, FrozenPath);
        var stored = StatementId.Create("sha256:" + new string('f', 64));
        AddState(fixture, FrozenPath, stored);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"frozen state {FrozenStatePathValue}", diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"stored={stored.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"actual={actual.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RejectsStateWhoseModuleDoesNotExist()
    {
        var fixture = new RuleFixture();
        const string missingModule = "D5/S0/Carrier/Missing.lean";
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(missingModule)).Value;
        fixture.Files[statePath] = StateText(StatementId.Create("sha256:" + new string('1', 64)));

        var diagnostic = Assert.Single(
            Evaluate(fixture, (statePath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"SL-008 frozen state {statePath}: module {missingModule} does not exist", diagnostic.Render());
    }

    [Fact]
    public void Sl008RejectsStateWhoseModuleIsNotClosed()
    {
        var fixture = new RuleFixture();
        fixture.SetRingDeclaration("openRing", "axiom", "fixtureAxiom");
        AddState(fixture, FrozenPath, ModuleStatementId(fixture, FrozenPath));

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(
            $"SL-008 frozen state {FrozenStatePathValue}: module {FrozenPath} has TruthState=Tail, expected Closed",
            diagnostic.Render());
    }

    [Fact]
    public void Sl008RejectsAcceptedFreezeWhosePinDiffersFromTheStateFragment()
    {
        var fixture = new RuleFixture();
        var statePin = ModuleStatementId(fixture, FrozenPath);
        var eventPin = StatementId.Create("sha256:" + new string('e', 64));
        AddState(fixture, FrozenPath, statePin);
        _ = AddFreeze(fixture, FrozenPath, eventPin);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"frozen state {FrozenStatePathValue}", diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"state={statePin.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"accepted={eventPin.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsHeaderOrCommentChangesWhenTheModulePinIsUnchanged()
    {
        var fixture = new RuleFixture();
        var pin = ModuleStatementId(fixture, FrozenPath);
        AddState(fixture, FrozenPath, pin, includeInBaseline: true);
        _ = AddFreeze(fixture, FrozenPath, pin);
        fixture.Files[FrozenPath] += "-- comment-only candidate change\n";

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

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
        string descriptorSelector,
        StatementId? statementId = null)
    {
        var path = RepoPath.CreateKnown(descriptorSelector);
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(
            path,
            fixture.Reports[descriptorSelector]);
        var material = new FrozenNodeMaterial(
            path,
            declarations,
            statementId ?? FrozenContentAddress.ComputeModuleStatementId(
                path,
                fixture.Reports[descriptorSelector]),
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

    private static StatementId ModuleStatementId(RuleFixture fixture, string modulePath)
    {
        var path = RepoPath.CreateKnown(modulePath);
        return FrozenContentAddress.ComputeModuleStatementId(path, fixture.Reports[modulePath]);
    }

    private static void AddState(
        RuleFixture fixture,
        string modulePath,
        StatementId statementId,
        bool includeInBaseline = false)
    {
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(modulePath)).Value;
        fixture.Files[statePath] = StateText(statementId);
        if (includeInBaseline)
        {
            fixture.Baseline[statePath] = fixture.Files[statePath];
            fixture.ForkPoint[statePath] = fixture.Files[statePath];
        }
    }

    private static string StateText(StatementId statementId) =>
        $"{{\"statement_id\":\"{statementId.Value}\"}}\n";

    private static SingleRuleEvaluation Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(changes)));

}
