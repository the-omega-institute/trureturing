using System.Text.Json;
using System.Text.Json.Nodes;
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
        var valid = Assert.Single(FrozenLedgerGenerator.Revocation(baseline, plan));
        var payload = JsonNode.Parse(valid.Payload.GetRawText())!.AsObject();
        payload["closure_hash"] = Sha256("forged-closure");
        var forged = LoadDrafts(
            BaseView(baselineCatalog),
            [new FrozenLedgerDraft("Revoke", JsonSerializer.SerializeToElement(payload))]);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(forged, baseline, BuildCatalog(), receipts.Store));

        Assert.Contains("closure", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }
}
