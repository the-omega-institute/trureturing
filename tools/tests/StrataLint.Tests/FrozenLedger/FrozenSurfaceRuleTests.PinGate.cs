using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed partial class FrozenSurfaceRuleTests
{
    [Fact]
    public void Sl008C6aBlocksAddedFreezeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddFreeze(fixture, FrozenPath);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(FrozenStatePathValue, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("run ledger-align --from-accepted", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6AllowsAddedFreezeWithMatchingFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var pin = ModuleStatementId(fixture, FrozenPath);
        var eventPath = AddFreeze(fixture, FrozenPath, pin);
        AddState(fixture, FrozenPath, pin);

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008C6bBlocksAddedFreezeWithMismatchedFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPin = ModuleStatementId(fixture, FrozenPath);
        var statePin = StatementId.Create("sha256:" + new string('e', 64));
        Assert.NotEqual(eventPin, statePin);
        var eventPath = AddFreeze(fixture, FrozenPath, eventPin);
        AddState(fixture, FrozenPath, statePin);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains($"selector={FrozenPath}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"event pin={eventPin.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"state pin={statePin.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6FailsClosedForAddedNonFreezeAcceptedEvent()
    {
        var fixture = new RuleFixture();
        var eventPath = AddNonFreezeAcceptedEvent(fixture, "Revoke");

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains("accepted event could not be loaded", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "content-addressed event type Revoke is not legal in ledger v5.",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6IgnoresUnchangedAcceptedFreezeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddFreeze(fixture, FrozenPath);
        fixture.Baseline[eventPath] = fixture.Files[eventPath];
        fixture.ForkPoint[eventPath] = fixture.Files[eventPath];

        var evaluation = Evaluate(fixture);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008C6FailsClosedForMalformedAddedAcceptedEvent()
    {
        var fixture = new RuleFixture();
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('d', 64));
        fixture.Files[eventPath] = "{}\n";

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains(
            "content-addressed event envelope has unknown, missing, or duplicate fields.",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6FailsClosedForGarbageEventTypeBeforePinChecks()
    {
        var fixture = new RuleFixture();
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('e', 64));
        fixture.Files[eventPath] = "{\"event_type\":\"Garbage\"}\n";

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains("accepted event could not be loaded", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "content-addressed event envelope has unknown, missing, or duplicate fields.",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    private static string AddNonFreezeAcceptedEvent(
        RuleFixture fixture,
        string eventType)
    {
        var freezePath = AddFreeze(fixture, FrozenPath);
        var envelope = JsonNode.Parse(fixture.Files[freezePath])!.AsObject();
        envelope["event_type"] = eventType;
        envelope.Remove("event_hash");
        var eventHash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEvent,
            StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(envelope)).AsSpan());
        envelope["event_hash"] = eventHash;
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(eventHash);
        fixture.Files.Remove(freezePath);
        fixture.Files[eventPath] = Encoding.UTF8.GetString(
            StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(envelope)).AsSpan());
        return eventPath;
    }
}
