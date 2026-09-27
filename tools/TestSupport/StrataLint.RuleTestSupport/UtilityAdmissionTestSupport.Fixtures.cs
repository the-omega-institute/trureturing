using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal static partial class UtilityAdmissionTestSupport
{
    internal const string Ordinary = "kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum";
    internal const string Refutes = "kind=certified-instance; basis=refutes=gid:" + Claim
        + "; result=" + Result + "; claim=" + Claim;

    internal static RuleFixture InstanceFixture(string? utility)
    {
        var fixture = new RuleFixture();
        fixture.Baseline.Remove(RuleFixture.RingPath);
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("generality: G", "generality: I", StringComparison.Ordinal)
            .Replace("def goldenRing : Nat := 0", "theorem fixed_sum : 17 + 4 = 21 := rfl", StringComparison.Ordinal);
        if (utility is not null) fixture.Files[RuleFixture.RingPath] = WithUtility(fixture.Files[RuleFixture.RingPath], utility);
        fixture.Reports[RuleFixture.RingPath] = new([], [new("fixed_sum", "theorem", "17 + 4 = 21", [])]);
        return fixture;
    }

    internal static string AddCandidateState(RuleFixture fixture)
    {
        var state = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[state] = "{\"statement_id\":\"sha256:" + new string('0', 64) + "\"}\n";
        return state;
    }

    internal static RawRepositorySnapshot Raw(Dictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    internal static RuleFixture RefutationFixture()
    {
        var fixture = InstanceFixture(Refutes);
        fixture.Reports[RuleFixture.RingPath] = new([], [
            new("proposed_law", "def", "Prop := False", []),
            new("refuted_law", "theorem", "Not proposed_law", []),
        ]) { Refutation = new(Claim, Result, true) };
        return fixture;
    }
}
