using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// A first review round on PR #2564 found two behaviours the command-path tests did not
/// pin: dropping Block from the blocking predicate survived, and removing both ThenBy
/// clauses survived because each of those tests raises exactly one observation. These
/// exercise the renderer directly so both mutations die.
public sealed class BackfillEffectRenderingTests
{
    [Fact]
    public void BlockingFindingStillThrowsSoTheGateCannotBeQuietlyOpened()
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            DigestionBackfillValidation.RenderOrThrow(
            [
                new RuleFinding("Meta/BACKFILL.yaml", "blocking claim", AdmissionEffect.Block),
            ]));
        Assert.Contains("SL-016 final ledger is invalid", exception.Message, StringComparison.Ordinal);
        Assert.Contains("blocking claim", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HumanGateFindingAlsoThrows()
    {
        Assert.Throws<InvalidOperationException>(() =>
            DigestionBackfillValidation.RenderOrThrow(
            [
                new RuleFinding("Meta/BACKFILL.yaml", "gated claim", AdmissionEffect.HumanGate),
            ]));
    }

    [Fact]
    public void ObservationsAreOrderedByPathThenMessageLikeCliApplication()
    {
        var rendered = DigestionBackfillValidation.RenderOrThrow(
        [
            new RuleFinding("Meta/zeta.yaml", "m", AdmissionEffect.Observe),
            new RuleFinding("Meta/alpha.yaml", "z second", AdmissionEffect.Observe),
            new RuleFinding("Meta/alpha.yaml", "a first", AdmissionEffect.Observe),
        ]);
        var lines = rendered.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(3, lines.Length);
        Assert.Contains("Meta/alpha.yaml", lines[0], StringComparison.Ordinal);
        Assert.Contains("a first", lines[0], StringComparison.Ordinal);
        Assert.Contains("Meta/alpha.yaml", lines[1], StringComparison.Ordinal);
        Assert.Contains("z second", lines[1], StringComparison.Ordinal);
        Assert.Contains("Meta/zeta.yaml", lines[2], StringComparison.Ordinal);
    }

    [Fact]
    public void BlockingWinsEvenWhenObservationsArePresent()
    {
        Assert.Throws<InvalidOperationException>(() =>
            DigestionBackfillValidation.RenderOrThrow(
            [
                new RuleFinding("Meta/BACKFILL.yaml", "observed", AdmissionEffect.Observe),
                new RuleFinding("Meta/BACKFILL.yaml", "blocking", AdmissionEffect.Block),
            ]));
    }
}
