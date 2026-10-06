using StrataLint.Engine;
using static StrataLint.TestSupport.UtilityAdmissionTestSupport;

namespace StrataLint.Rules.Tests;

public sealed class UtilityScopeRejectProbe
{
    [Fact]
    public void InstalledUtilityTaskTargetRejectsMissingTaskWithoutAnyDigestionLedger()
    {
        var fixture = new RuleFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
            foreach (var path in files.Keys.Where(path => path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                || path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal)).ToArray())
                files.Remove(path);
        fixture.Files[RuleFixture.RingPath] = WithUtility(fixture.Files[RuleFixture.RingPath],
            "kind=checker; basis=terminal=task:D5-T0098; instance=D5/S0/Carrier/Ring.goldenRing");
        var diagnostics = EvaluateFirstFreeze(fixture);
        AssertBlockedObservationPair(diagnostics, "UTILITY-TARGET-DANGLING", "kind=checker basis=terminal target=task:D5-T0098");
    }
}
