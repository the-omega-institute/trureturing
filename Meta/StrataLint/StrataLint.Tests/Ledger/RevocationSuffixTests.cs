using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class RevocationTests
{
    [Fact]
    public void CandidateClosureHashIsRecomputedAndMustMatchExactly()
    {
        var baselineCatalog = BuildCatalog(Module("A"));
        var baseline = Genesis(baselineCatalog);
        var node = Assert.Single(baseline.ActiveFrozenNodes);
        var receipts = ReceiptStore(baseline, KernelFailure(node));
        var evidence = ValidateEvidence(receipts.Evidence[0], baseline, receipts.Store);
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(baseline, new[] { evidence })).Capability;
        var valid = FrozenLedgerGenerator.AppendRevocation(baseline, plan);
        var last = Lines(valid)[^1];
        using var document = JsonDocument.Parse(last.AsMemory(0, last.Length - 1));
        var payload = JsonNode.Parse(document.RootElement.GetProperty("payload").GetRawText())!.AsObject();
        payload["closure_hash"] = Sha256("forged-closure");
        var forgedLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Revoke",
            JsonSerializer.SerializeToElement(payload),
            baseline.HeadHash,
            baseline.Events.Length).Bytes;
        var forged = baseline.RawBytes.Concat(forgedLine).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(Load(forged), baseline, BuildCatalog(), receipts.Store));

        Assert.Contains("closure", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void LedgerAndHarnessChangesAreForbiddenMixedAtThePhaseZeroHook()
    {
        var changes = RawChangeSet.Create(new[]
        {
            FrozenLedgerChangeClassifier.LedgerPath,
            RuleFixture.SyntheticProtectedPath,
        });

        Assert.IsType<FrozenLedgerChangeOutcome.ForbiddenMixed>(
            FrozenLedgerChangeClassifier.Classify(changes));
    }
}
