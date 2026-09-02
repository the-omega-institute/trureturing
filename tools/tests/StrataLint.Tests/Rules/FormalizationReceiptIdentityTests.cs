using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FormalizationReceiptIdentityTests
{
    private const int RuleNumber = 31;
    private const string BareAtomId =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string OtherBareAtomId =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    private const string ThirdBareAtomId =
        "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    private const string CanonicalPath =
        "Meta/Digestion/formalizations/" + BareAtomId + ".v1.json";
    private const string OtherCanonicalPath =
        "Meta/Digestion/formalizations/" + OtherBareAtomId + ".v1.json";
    private const string ThirdCanonicalPath =
        "Meta/Digestion/formalizations/" + ThirdBareAtomId + ".v1.json";
    private const string LegacyAtomId = "generic-residual-" + BareAtomId;
    private const string LegacyPath =
        "Meta/Digestion/formalizations/" + LegacyAtomId + ".v1.json";
    private const string UnrelatedPath = "notes/unrelated.txt";
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";

    [Fact]
    public void LegacyNamedReceiptIsRejected()
    {
        var fixture = new RuleFixture();
        fixture.Files[LegacyPath] = Receipt(LegacyAtomId);

        Assert.Equal(1, CountFindings(Execute(fixture, LegacyPath)));
    }

    [Fact]
    public void CandidateReceiptLoaderRejectsPathThatDoesNotMatchRawSha256()
    {
        var snapshot = DigestionTestSupport.Snapshot(
            (LegacyPath, Encoding.UTF8.GetBytes(Receipt(LegacyAtomId))));

        var exception = Assert.Throws<FormatException>(() =>
            DigestionFormalizationReceipt.Load(snapshot, LegacyPath));

        Assert.Contains(CanonicalPath, exception.Message, StringComparison.Ordinal);
        Assert.Contains("raw_sha256", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReceiptFileNameMustEqualRawSha256()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = Receipt(BareAtomId, OtherBareAtomId);

        Assert.Contains(
            Findings(Execute(fixture, CanonicalPath)),
            diagnostic => diagnostic.Path == CanonicalPath
                && diagnostic.Message.Contains(OtherCanonicalPath, StringComparison.Ordinal)
                && diagnostic.Message.Contains("raw_sha256", StringComparison.Ordinal));
    }

    [Fact]
    public void TwoPathsForSameRawSha256AreRejectedEvenWhenAtomIdsDiffer()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = Receipt(
            BareAtomId,
            BareAtomId,
            "D5/S0/Carrier/Ring.goldenRing");
        fixture.Files[LegacyPath] = Receipt(
            LegacyAtomId,
            BareAtomId,
            "D5/S0/Carrier/ValuesBinding.fixtureValue");

        Assert.Contains(
            Findings(Execute(fixture, CanonicalPath, LegacyPath)),
            diagnostic => diagnostic.Message.Contains(
                $"raw_sha256 sha256:{BareAtomId} must be unique",
                StringComparison.Ordinal)
                && diagnostic.Message.Contains(CanonicalPath, StringComparison.Ordinal)
                && diagnostic.Message.Contains(LegacyPath, StringComparison.Ordinal));
    }

    [Fact]
    public void ReceiptAtomIdMustMatchBareHexFileName()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = Receipt(OtherBareAtomId);

        Assert.Equal(1, CountFindings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    public void CompliantBareHexReceiptIsAdmitted()
    {
        var fixture = new RuleFixture();
        fixture.Files[CanonicalPath] = Receipt(BareAtomId);

        Assert.Equal(0, CountFindings(Execute(fixture, CanonicalPath)));
    }

    [Fact]
    [BaseFactScopeProbe(31)]
    public void Sl031ScopesFindingsToChangedReceiptAndMatchingRawSha256Group()
    {
        var unrelated = new RuleFixture();
        SetHistorical(unrelated, CanonicalPath, Receipt(BareAtomId, OtherBareAtomId));
        unrelated.Files[UnrelatedPath] = "candidate\n";
        Assert.Equal(0, CountFindings(Execute(unrelated, UnrelatedPath)));

        var differentRaw = new RuleFixture();
        SetHistorical(differentRaw, CanonicalPath, Receipt(BareAtomId, OtherBareAtomId));
        differentRaw.Files[ThirdCanonicalPath] = Receipt(ThirdBareAtomId, ThirdBareAtomId);
        Assert.Equal(0, CountFindings(Execute(differentRaw, ThirdCanonicalPath)));

        var implementation = new RuleFixture();
        SetHistorical(implementation, CanonicalPath, Receipt(BareAtomId, OtherBareAtomId));
        Assert.Equal(0, CountFindings(Execute(implementation, RuleImplementationPath)));

        var matchingRaw = new RuleFixture();
        SetHistorical(matchingRaw, CanonicalPath, Receipt(BareAtomId));
        matchingRaw.Files[LegacyPath] = Receipt(
            LegacyAtomId,
            BareAtomId,
            "D5/S0/Carrier/ValuesBinding.fixtureValue");
        Assert.Contains(
            Findings(Execute(matchingRaw, LegacyPath)),
            diagnostic => diagnostic.Message.Contains(
                $"raw_sha256 sha256:{BareAtomId} must be unique",
                StringComparison.Ordinal)
                && diagnostic.Message.Contains(CanonicalPath, StringComparison.Ordinal)
                && diagnostic.Message.Contains(LegacyPath, StringComparison.Ordinal));
    }

    private static void SetHistorical(
        RuleFixture fixture,
        string path,
        string contents)
    {
        fixture.Baseline[path] = contents;
        fixture.ForkPoint[path] = contents;
        fixture.Files[path] = contents;
    }

    private static string Receipt(string atomId) => Receipt(atomId, BareAtomId);

    private static string Receipt(string atomId, string rawAtomId) =>
        Receipt(atomId, rawAtomId, "D5/S0/Carrier/Ring.goldenRing");

    private static string Receipt(string atomId, string rawAtomId, string primaryGid) =>
        Encoding.UTF8.GetString(DigestionFormalizationReceipt.Write(
            new DigestionFormalizationReceipt(
                atomId,
                primaryGid,
                new DigestionFormalizationSignature("goldenRing", "def", "Nat"),
                "sha256:" + rawAtomId,
                "sha256:" + rawAtomId)).AsSpan());

    private static CompletedRuleSet Execute(RuleFixture fixture, params string[] changedPaths)
    {
        var outcome = RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create(changedPaths)));
        if (outcome is RuleExecutionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail("INFRA: " + failure.Message);
        }

        return Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
    }

    private static int CountFindings(CompletedRuleSet completed) =>
        Findings(completed).Length;

    private static Diagnostic[] Findings(CompletedRuleSet completed) =>
        completed.Diagnostics
            .Where(diagnostic => diagnostic.RuleId == RuleId.CreateKnown(RuleNumber))
            .ToArray();
}
