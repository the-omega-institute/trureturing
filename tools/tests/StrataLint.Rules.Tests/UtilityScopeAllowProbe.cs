using StrataLint.Engine;
using static StrataLint.TestSupport.UtilityAdmissionTestSupport;

namespace StrataLint.Rules.Tests;

public sealed class UtilityScopeAllowProbe
{
    [Fact]
    public void InstalledUtilityTaskTargetAllowsDeclaredTaskWithoutAnyDigestionLedger()
    {
        var fixture = new RuleFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
            foreach (var path in files.Keys.Where(path => path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                || path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal)).ToArray())
                files.Remove(path);
        fixture.AddSyntheticUnregisteredFrontierTask("D5-T0098");
        fixture.Files[RuleFixture.RingPath] = WithUtility(fixture.Files[RuleFixture.RingPath],
            "kind=checker; basis=terminal=task:D5-T0098; instance=D5/S0/Carrier/Ring.goldenRing");
        var diagnostics = EvaluateFirstFreeze(fixture);
        AssertSoftObservation(diagnostics, "kind=checker basis=terminal target=task:D5-T0098");
    }
}
