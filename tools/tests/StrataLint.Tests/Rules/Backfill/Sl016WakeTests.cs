using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// Which candidate changes wake SL-016. The rule catalog skips a rule whose IsAffectedBy is
/// false, so every input class whose change can move the digestion projection needs a named
/// pin here: a trigger that silently stops matching produces no symptom at all.
/// </summary>
public sealed class Sl016WakeTests
{
    [Fact]
    public void LeanToolchainChangeWakesSl016BecauseItsLeanReportInputCanDrift()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(["lean-toolchain"]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void TheoryDocumentChangeWakesSl016BecauseItsAtomProjectionCanDrift()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["docs/develop/theory/INTERFACE_PAPER.md"]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void UnenumeratedTheoryDocumentChangeWakesSl016BecauseVolumeNamesCannotBeListed()
    {
        // A third-party volume name cannot be pre-enumerated in registry.yaml; the trigger
        // must come from the theory path rule, not from a representative list.
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["docs/develop/theory/A_VOLUME_THAT_IS_IN_NO_LIST.md"]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void EveryOpaqueDigestionInputWakesSl016()
    {
        // IsOpaque names the three input classes whose change can move the atom projection.
        // Each must wake the rule; the theory class does so through its own path predicate,
        // the other two through their own disjuncts. Pinned here so that removing any one of
        // them is a named failure rather than a silent skip.
        var fixture = new RuleFixture();

        foreach (var path in new[]
                 {
                     "docs/develop/theory/ANY_VOLUME.md",
                     TheoryAtomizerDataLoader.DataPath,
                     $"{DigestionCasStore.RootPath}0000000000000000000000000000000000000000000000000000000000000000",
                 })
        {
            Assert.True(
                DigestionOpaquePathPolicy.IsOpaque(RepoPath.CreateKnown(path)),
                $"{path} is expected to be an opaque digestion input");
            Assert.True(
                BackfillInventoryRule.IsAffectedBy(fixture.Build(RawChangeSet.Create([path]))),
                $"{path} is an opaque digestion input and must wake SL-016");
        }
    }

    [Fact]
    public void AtomizerImplementationChangeWakesSl016BecauseItsProjectionCanDrift()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs"]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }
}
