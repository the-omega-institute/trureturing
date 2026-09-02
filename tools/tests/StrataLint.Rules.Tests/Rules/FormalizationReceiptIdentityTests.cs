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
    private const string CanonicalPath =
        "Meta/Digestion/formalizations/" + BareAtomId + ".v1.json";
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
    public void Sl031FormalizationReceiptIdentityScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        var unrelated = new RuleFixture();
        SetHistorical(unrelated, CanonicalPath, Receipt(OtherBareAtomId));
        unrelated.Files[UnrelatedPath] = "candidate\n";
        Assert.Equal(0, CountFindings(Execute(unrelated, UnrelatedPath)));

        var changed = new RuleFixture();
        SetHistorical(changed, CanonicalPath, Receipt(BareAtomId));
        changed.Files[CanonicalPath] = Receipt(OtherBareAtomId);
        Assert.Equal(1, CountFindings(Execute(changed, CanonicalPath)));

        var implementation = new RuleFixture();
        SetHistorical(implementation, CanonicalPath, Receipt(OtherBareAtomId));
        Assert.Equal(1, CountFindings(Execute(implementation, RuleImplementationPath)));
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

    private static string Receipt(string atomId) =>
        Encoding.UTF8.GetString(DigestionFormalizationReceipt.Write(
            new DigestionFormalizationReceipt(
                atomId,
                "D5/S0/Carrier/Ring.goldenRing",
                new DigestionFormalizationSignature("goldenRing", "def", "Nat"),
                "sha256:" + BareAtomId,
                "sha256:" + BareAtomId)).AsSpan());

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
        completed.Diagnostics.Count(diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(RuleNumber));
}
