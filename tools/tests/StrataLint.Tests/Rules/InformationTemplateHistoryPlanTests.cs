using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DeclaredTemplateReviewTests;

namespace StrataLint.Tests;

public sealed class InformationTemplateHistoryPlanTests
{
    internal const string Base = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    internal const string Seed = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Fact]
    public void predicate_preserves_inactive_fast_path_and_all_reader_triggers()
    {
        var inactive = Files(Seed);
        var active = Files(Seed, true);
        var rows = new Dictionary<string, string>(inactive)
            { [InformationTemplateDebtStore.Root + "unexpected.txt"] = "row population" };
        var missing = new Dictionary<string, string>(inactive);
        missing.Remove(InformationTemplateDebtStore.ActivationPath);
        var changed = Files(Base);
        var cases = new[] { (missing, inactive, false), (inactive, missing, false),
            (inactive, inactive, false), (active, inactive, true), (inactive, active, true),
            (rows, inactive, true), (inactive, rows, true), (inactive, changed, true) };
        foreach (var (before, after, required) in cases)
        {
            var addresses = 0;
            var plan = InformationTemplateHistoryPlan.Create(Base, Tree(before), Tree(after), "check",
                () => { addresses++; return new string('c', 64); }, "Linux", "ARM64");
            Assert.True(plan.Required == required, "[FAIL] predicate_preserves_inactive_fast_path_and_all_reader_triggers");
            Assert.Equal(required ? 1 : 0, addresses);
            Assert.Equal(required ? new[] { Seed, Base } : [], plan.Targets.Select(t => t.Revision));
        }
        Assert.Single(InformationTemplateHistoryPlan.Create(Base, Tree(Files(Base)), Tree(active), "check",
            () => new string('c', 64), "Linux", "ARM64").Targets);
        Assert.Equal(new[] { Seed }, InformationTemplateHistoryPlan.Create(Base, Tree(inactive), Tree(inactive), "seed",
            () => new string('c', 64), "Linux", "ARM64").Targets.Select(t => t.Revision));
        Assert.Equal(2, InformationTemplateHistoryPlan.Create(Base, Tree(inactive), Tree(inactive), "discharge",
            () => new string('c', 64), "Linux", "ARM64").Targets.Length);
        var malformed = new Dictionary<string, string>(inactive) { [InformationTemplateDebtStore.ActivationPath] = "{}" };
        Assert.Throws<FormatException>(() => InformationTemplateHistoryPlan.Create(Base, Tree(inactive), Tree(malformed), "check",
            () => throw new InvalidOperationException("must not hash"), "Linux", "ARM64"));
        Assert.Throws<FormatException>(() => InformationTemplateHistoryPlan.Create("main", Tree(inactive), Tree(inactive), "check",
            () => "", "Linux", "ARM64"));
    }

    [Fact]
    public void producer_records_bind_bytes_modes_absence_and_pair_revision()
    {
        var records = ImmutableArray.Create(
            new InformationTemplateProducerRecord("tools/inspect.sh", "100755", new string('a', 64)),
            new InformationTemplateProducerRecord("optional.toml", "absent", null));
        var bytes = InformationTemplateHistoryPlan.ProducerBytes(records);
        Assert.Equal("{\"records\":[{\"mode\":\"absent\",\"path\":\"optional.toml\",\"sha256\":null},{\"mode\":\"100755\",\"path\":\"tools/inspect.sh\",\"sha256\":\""
            + new string('a', 64) + "\"}],\"schema\":\"information-template-history-producer-v1\"}\n", Encoding.UTF8.GetString(bytes.AsSpan()));
        var producer = InformationTemplateJson.Sha256(bytes.AsSpan());
        Assert.Equal(producer, InformationTemplateJson.Sha256(InformationTemplateHistoryPlan.ProducerBytes(records.Reverse()).AsSpan()));
        foreach (var changed in new[] { records.SetItem(0, records[0] with { Mode = "100644" }),
            records.SetItem(0, records[0] with { Sha256 = new string('b', 64) }), records.RemoveAt(1) })
            Assert.NotEqual(producer, InformationTemplateJson.Sha256(InformationTemplateHistoryPlan.ProducerBytes(changed).AsSpan()));
        var first = InformationTemplateHistoryPlan.Target(producer, Seed, "Linux", "ARM64");
        Assert.Equal($"it-history-v1-Linux-ARM64-{producer}-{Seed}", first.CacheKey);
        Assert.NotEqual(first.Pair, InformationTemplateHistoryPlan.Target(producer, Base, "Linux", "ARM64").Pair);
        Assert.Equal(first.Pair, InformationTemplateHistoryPlan.Target(producer, Seed, "macOS", "ARM64").Pair);
    }

    [Fact]
    public void rule_historical_reader_is_included_by_planner()
    {
        var calls = 0;
        foreach (var activeBefore in new[] { false, true })
        foreach (var activeAfter in new[] { false, true })
        foreach (var rowsBefore in new[] { false, true })
        foreach (var rowsAfter in new[] { false, true })
        {
            var before = Files(Seed, activeBefore);
            var after = Files(Seed, activeAfter);
            const string row = "Golden/InformationTemplateDebt/rows/fixture.json";
            if (rowsBefore) before[row] = "{}";
            if (rowsAfter) after[row] = "{}";
            var plan = InformationTemplateHistoryPlan.Create(Base, Tree(before), Tree(after), "check",
                () => new string('c', 64), "Linux", "ARM64");
            var observed = 0;
            var history = new InformationTemplateEvidenceContext(Base, _ =>
            {
                observed++; calls++;
                return new(Tree(before), Report(before));
            });
            DeclaredTemplateBindingRule.Evaluate(Context(before, after, Report(after), [row], history));
            Assert.True(observed == 0 || plan.Required, "[FAIL] rule_historical_reader_is_included_by_planner");
        }
        Assert.True(calls > 0, "[FAIL] reader callback must be exercised");
    }
}
