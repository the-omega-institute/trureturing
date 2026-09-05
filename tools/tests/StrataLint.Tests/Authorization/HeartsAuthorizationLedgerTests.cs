using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class HeartsAuthorizationLedgerTests
{
    [Fact]
    public void ReadsCanonicalFourColumnLedger()
    {
        var entry = Assert.Single(HeartsAuthorizationLedger.Read(
            """
            # Hearts Authorizations

            | date | authorization | statement | statement-sha256 |
            |---|---|---|---|
            | 2026-07-16 | "虽然我认为1/2离线零点存在,但我们去证明黎曼猜想没问题,因为这个过程会产生大量truth" | D5.X_Frontier.Hearts.o6WeilPositivityStatement | ed92660e5db32dd93582415392e52433622d33f8cbed1d5935f26cacba5133cd |
            """ + "\n"));

        Assert.Equal("2026-07-16", entry.Date);
        Assert.Equal(
            "\"虽然我认为1/2离线零点存在,但我们去证明黎曼猜想没问题,因为这个过程会产生大量truth\"",
            entry.Authorization);
        Assert.Equal(
            "D5.X_Frontier.Hearts.o6WeilPositivityStatement",
            entry.StatementName);
        Assert.Equal(
            "ed92660e5db32dd93582415392e52433622d33f8cbed1d5935f26cacba5133cd",
            entry.StatementSha256);
    }

    [Fact]
    public void Sl008RejectsMalformedCandidateAuthorizationLedger()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[HeartsAuthorizationLedger.Path] = HeartsAuthorizationLedger.Header;
        fixture.ForkPoint[HeartsAuthorizationLedger.Path] = HeartsAuthorizationLedger.Header;
        fixture.Files[HeartsAuthorizationLedger.Path] =
            HeartsAuthorizationLedger.Header + "not a ledger row\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(HeartsAuthorizationLedger.Path, RawChangeKind.Modified)])));

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == HeartsAuthorizationLedger.Path
            && diagnostic.Message.Contains("exactly four columns", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl008DoesNotRevalidateMalformedAuthorizationLedgerButFailsClosedForAddedAcceptedEvent()
    {
        var fixture = new RuleFixture();
        var malformed = HeartsAuthorizationLedger.Header + "not a ledger row\n";
        fixture.Files[HeartsAuthorizationLedger.Path] = malformed;
        fixture.Baseline[HeartsAuthorizationLedger.Path] = malformed;
        fixture.ForkPoint[HeartsAuthorizationLedger.Path] = malformed;
        var acceptedPath = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('a', 64));
        fixture.Files[acceptedPath] = "candidate accepted event\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(acceptedPath, RawChangeKind.Added)])));

        Assert.DoesNotContain(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == HeartsAuthorizationLedger.Path);
        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(acceptedPath, diagnostic.Path);
        Assert.Contains("accepted event could not be loaded", diagnostic.Message, StringComparison.Ordinal);
    }
}
