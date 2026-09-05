using StrataLint.Engine;
using static StrataLint.Tests.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed class UtilityAdmissionReachabilityTests
{
    [Fact]
    public void ConsumerWithoutImportPathIsBlocked()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-CONSUMER-UNREACHABLE module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"consumer_module={RuleFixture.ValuesBindingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void SameModuleConsumerIsAllowed()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/Ring.goldenRing");

        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void TransitiveConsumerIsAllowed()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };
        fixture.Reports[intermediatePath] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [new LeanDeclaration("intermediate", "def", "Unit", [])]);

        var diagnostics = EvaluateFirstFreeze(fixture);

        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void MissingIntermediateReportIsUnknownNotUnreachable()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"reason=consumer-path-input-missing:{intermediatePath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "UTILITY-CONSUMER-UNREACHABLE",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ErroredIntermediateReportCannotProveReachability()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };
        fixture.Reports[intermediatePath] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [],
            Error: "synthetic elaboration failure");

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"reason=consumer-path-input-missing:{intermediatePath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "UTILITY-CONSUMER-UNREACHABLE",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingReportInputFailsClosedInsteadOfMeaningZeroEdges()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Reports.Remove(RuleFixture.RingPath);

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("reason=current-lean-report-missing", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("UTILITY-CONSUMER-UNREACHABLE", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("instance", "D5/S0/Carrier/Ring.missing")]
    [InlineData("premises", "D5/S0/Carrier/Ring.goldenRing,D5/S0/Carrier/Ring.missing")]
    [InlineData("result", "D5/S0/Carrier/Ring.missing")]
    public void DanglingOptionalDeclarationIsBlocked(string key, string value)
    {
        var kind = key == "premises" ? "numeric-reduction" : "certified-instance";
        var diagnostic = Assert.Single(EvaluateFirstFreeze(
            $"kind={kind}; basis=refutes=gid:D5/S0/Carrier/Ring.goldenRing; {key}={value}"),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-TARGET-DANGLING module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("target=D5/S0/Carrier/Ring.missing", diagnostic.Message, StringComparison.Ordinal);
    }
}
