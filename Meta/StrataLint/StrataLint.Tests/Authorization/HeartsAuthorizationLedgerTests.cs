using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class HeartsAuthorizationLedgerTests
{
    private const string StatementName =
        "D5.X_Frontier.Hearts.o6WeilPositivityStatement";

    private const string StatementSha256 =
        "ed92660e5db32dd93582415392e52433622d33f8cbed1d5935f26cacba5133cd";

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
        Assert.Equal(StatementName, entry.StatementName);
        Assert.Equal(StatementSha256, entry.StatementSha256);
    }

    [Fact]
    public void Sl008AllowsOneExactlyAuthorizedStatementAppend()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var authorized = Declaration(StatementName, "statement-v1(type=O6)");
        var fixture = HeartsFixture([frozen], [frozen, authorized]);
        var ledger = Ledger((authorized, StatementSha(authorized)));
        fixture.Baseline[HeartsAuthorizationLedger.Path] = ledger;
        fixture.Files[HeartsAuthorizationLedger.Path] = ledger;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsStatementAppendWithoutAuthorizationEntry()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var unauthorized = Declaration(StatementName, "statement-v1(type=O6)");
        var fixture = HeartsFixture([frozen], [frozen, unauthorized]);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message == "semantic declaration identities and types are frozen");
    }

    [Fact]
    public void Sl008RejectsStatementAppendWithMismatchedSha256()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var unauthorized = Declaration(StatementName, "statement-v1(type=O6)");
        var fixture = HeartsFixture([frozen], [frozen, unauthorized]);
        var ledger = Ledger((unauthorized, new string('0', 64)));
        fixture.Baseline[HeartsAuthorizationLedger.Path] = ledger;
        fixture.Files[HeartsAuthorizationLedger.Path] = ledger;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message == "semantic declaration identities and types are frozen");
    }

    [Fact]
    public void Sl008RejectsAuthorizedStatementWithPiggybackDeclaration()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var authorized = Declaration(StatementName, "statement-v1(type=O6)");
        var piggyback = Declaration(
            "D5.X_Frontier.Hearts.piggyback",
            "statement-v1(type=False)");
        var fixture = HeartsFixture([frozen], [frozen, authorized, piggyback]);
        var ledger = Ledger((authorized, StatementSha(authorized)));
        fixture.Baseline[HeartsAuthorizationLedger.Path] = ledger;
        fixture.Files[HeartsAuthorizationLedger.Path] = ledger;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message == "semantic declaration identities and types are frozen");
    }

    [Fact]
    public void Sl008RejectsRewrittenAuthorizationHistory()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var authorized = Declaration(StatementName, "statement-v1(type=O6)");
        var fixture = HeartsFixture([frozen], [frozen]);
        var baselineLedger = Ledger((authorized, StatementSha(authorized)));
        fixture.Baseline[HeartsAuthorizationLedger.Path] = baselineLedger;
        fixture.Files[HeartsAuthorizationLedger.Path] = baselineLedger.Replace(
            "\"authorized\"",
            "\"forged\"",
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == HeartsAuthorizationLedger.Path
            && diagnostic.Message == "Hearts authorization ledger is append-only");
    }

    [Fact]
    public void Sl008RejectsDeletedAuthorizationHistory()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var authorized = Declaration(StatementName, "statement-v1(type=O6)");
        var fixture = HeartsFixture([frozen], [frozen]);
        fixture.Baseline[HeartsAuthorizationLedger.Path] =
            Ledger((authorized, StatementSha(authorized)));
        fixture.Files.Remove(HeartsAuthorizationLedger.Path);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == HeartsAuthorizationLedger.Path
            && diagnostic.Message == "Hearts authorization ledger is append-only");
    }

    [Fact]
    public void Sl008AllowsCanonicalAuthorizationHistoryAppend()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var first = Declaration(StatementName, "statement-v1(type=O6)");
        var second = Declaration(
            "D5.X_Frontier.Hearts.futureStatement",
            "statement-v1(type=Future)");
        var fixture = HeartsFixture([frozen], [frozen]);
        var baselineLedger = Ledger((first, StatementSha(first)));
        fixture.Baseline[HeartsAuthorizationLedger.Path] = baselineLedger;
        fixture.Files[HeartsAuthorizationLedger.Path] = baselineLedger
            + AuthorizationRow(second, StatementSha(second));

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsMalformedAuthorizationLedger()
    {
        var frozen = Declaration("D5.X_Frontier.Hearts.frozen", "statement-v1(type=True)");
        var fixture = HeartsFixture([frozen], [frozen]);
        fixture.Files[HeartsAuthorizationLedger.Path] =
            HeartsAuthorizationLedger.Header + "not a ledger row\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == HeartsAuthorizationLedger.Path
            && diagnostic.Message.Contains("exactly four columns", StringComparison.Ordinal));
    }

    private static LeanDeclaration Declaration(string name, string type) => new(
        name,
        "theorem",
        type,
        ImmutableArray.Create("sorryAx"));

    private static RuleFixture HeartsFixture(
        LeanDeclaration[] baseline,
        LeanDeclaration[] candidate)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.HeartsPath] = "baseline Hearts\n";
        fixture.Files[RuleFixture.HeartsPath] = "candidate Hearts\n";
        fixture.BaselineReports[RuleFixture.HeartsPath] = new LeanFileReport(
            ImmutableArray<string>.Empty,
            baseline.ToImmutableArray());
        fixture.Reports[RuleFixture.HeartsPath] = new LeanFileReport(
            ImmutableArray<string>.Empty,
            candidate.ToImmutableArray());
        return fixture;
    }

    private static string Ledger(params (LeanDeclaration Declaration, string Sha256)[] entries) =>
        HeartsAuthorizationLedger.Header
        + string.Concat(entries.Select(entry => AuthorizationRow(entry.Declaration, entry.Sha256)));

    private static string AuthorizationRow(LeanDeclaration declaration, string sha256) =>
        $"| 2026-07-16 | \"authorized\" | {declaration.Name} | {sha256} |\n";

    private static string StatementSha(LeanDeclaration declaration)
    {
        Assert.True(RepoPath.TryCreate(RuleFixture.HeartsPath, out var path));
        var statement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            path,
            new LeanFileReport(ImmutableArray<string>.Empty, [declaration])));
        return statement.StatementId.Value["sha256:".Length..];
    }
}
