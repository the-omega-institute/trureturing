using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl017LiteratureScopeTests
{
    private const string InvalidQueries = """
        schema_version: 1
        queries:
          - id: bad-query
            target_gid: D5/S0/Carrier/Ring
        """;

    [Fact]
    public void Sl017SkipsInvalidLiteratureWhenOnlyUnrelatedManagedLeanChanges()
    {
        var fixture = Fixture();
        var changedPath = RuleFixture.ValuesBindingPath;

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([changedPath])))).Capability;

        Assert.DoesNotContain(RuleId.CreateKnown(17), completed.ExecutedRules);
        Assert.DoesNotContain(
            completed.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(17));
    }

    [Fact]
    public void Sl017StillExecutesWhenItsImplementationClosureChanges()
    {
        var fixture = Fixture();
        const string implementationPath =
            "tools/StrataLint.Engine/Rules/RepositoryRules.Content.cs";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(
                fixture.Build(RawChangeSet.Create([implementationPath])))).Capability;

        Assert.Contains(RuleId.CreateKnown(17), completed.ExecutedRules);
        Assert.Contains(
            completed.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(17));
    }

    private static RuleFixture Fixture()
    {
        var fixture = new RuleFixture();
        fixture.Files["Library/queries.yaml"] = InvalidQueries;
        fixture.Baseline["Library/queries.yaml"] = InvalidQueries;
        fixture.ForkPoint["Library/queries.yaml"] = InvalidQueries;
        return fixture;
    }
}
