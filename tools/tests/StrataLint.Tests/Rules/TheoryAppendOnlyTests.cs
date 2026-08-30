using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

/// <summary>
/// SL-029 keeps theory volumes append-only. A volume grows by publishing new prose at its end;
/// an erratum is published the same way, as new text, so that a claim already digested keeps the
/// bytes it was digested from. The rule therefore admits exactly one shape of change — the base
/// bytes remain a prefix of the candidate bytes — and rejects in-place edits, truncation, and
/// deletion alike. Both sides are nailed here: a gate that rejected everything would satisfy the
/// rejection cases alone.
/// </summary>
public sealed class TheoryAppendOnlyTests
{
    private const string VolumePath = "docs/develop/theory/PROBE_VOLUME.md";
    private const string OtherVolumePath = "docs/develop/theory/OTHER_VOLUME.md";
    private const string Message = "theory volumes are append-only";
    private const int RuleNumber = 29;
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";

    [Fact]
    public void AppendingToAVolumeIsAdmitted()
    {
        var fixture = Volume("# Volume\n\nfirst part\n");
        fixture.Files[VolumePath] = "# Volume\n\nfirst part\nsecond part\n";

        Assert.Equal(0, CountFindings(Execute(fixture, VolumePath)));
    }

    [Fact]
    public void EditingExistingProseIsRejected()
    {
        var fixture = Volume("# Volume\n\nfirst part\n");
        fixture.Files[VolumePath] = "# Volume\n\nFIRST part\n";

        Assert.Equal(1, CountFindings(Execute(fixture, VolumePath)));
    }

    [Fact]
    public void TruncatingAVolumeIsRejected()
    {
        var fixture = Volume("# Volume\n\nfirst part\nsecond part\n");
        fixture.Files[VolumePath] = "# Volume\n\nfirst part\n";

        Assert.Equal(1, CountFindings(Execute(fixture, VolumePath)));
    }

    [Fact]
    public void DeletingAVolumeIsRejected()
    {
        var fixture = Volume("# Volume\n\nfirst part\n");
        fixture.Files.Remove(VolumePath);

        Assert.Equal(1, CountFindings(Execute(fixture, VolumePath)));
    }

    [Fact]
    public void AVolumeOutsideTheDeltaIsNotJudged()
    {
        var fixture = Volume("# Volume\n\nfirst part\n");
        fixture.Files[OtherVolumePath] = "# Other\n";

        Assert.Equal(0, CountFindings(Execute(fixture, OtherVolumePath)));
    }

    [Fact]
    public void AddingANewVolumeIsAdmitted()
    {
        var fixture = new RuleFixture();
        fixture.Files[VolumePath] = "# Volume\n\nfirst part\n";

        Assert.Equal(0, CountFindings(Execute(fixture, VolumePath)));
    }

    [Fact]
    public void EditingAFileOutsideTheTheoryTreeIsNotThisRulesBusiness()
    {
        var fixture = new RuleFixture();
        fixture.Baseline["docs/NOTES.md"] = "before\n";
        fixture.ForkPoint["docs/NOTES.md"] = "before\n";
        fixture.Files["docs/NOTES.md"] = "after\n";

        Assert.Equal(0, CountFindings(Execute(fixture, "docs/NOTES.md")));
    }

    /// <summary>
    /// The differential scope probe the ratchet requires: a volume nobody touched is not judged,
    /// the one in the delta is, and touching the rule's own implementation puts every volume back
    /// in scope because the predicate that judged them has changed.
    /// </summary>
    [Fact]
    [BaseFactScopeProbe(29)]
    public void Sl029TheoryAppendOnlyScopesVolumesAndKeepsDeltaAndImplementationRechecks()
    {
        var unrelated = Volume("# Volume\n\nfirst part\n");
        unrelated.Files[OtherVolumePath] = "# Other\n";
        Assert.Equal(0, CountFindings(Execute(unrelated, OtherVolumePath)));

        var changed = Volume("# Volume\n\nfirst part\n");
        changed.Files[VolumePath] = "# Volume\n\nFIRST part\n";
        Assert.Equal(1, CountFindings(Execute(changed, VolumePath)));

        var implementation = Volume("# Volume\n\nfirst part\n");
        implementation.Files[VolumePath] = "# Volume\n\nFIRST part\n";
        Assert.Equal(1, CountFindings(Execute(implementation, RuleImplementationPath)));
    }

    private static RuleFixture Volume(string text)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[VolumePath] = text;
        fixture.ForkPoint[VolumePath] = text;
        fixture.Files[VolumePath] = text;
        return fixture;
    }

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
            diagnostic.RuleId == RuleId.CreateKnown(RuleNumber)
            && diagnostic.Message.Contains(Message, StringComparison.Ordinal));
}
