using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class LeanCacheProvisionerTests
{
    private static void AssertCacheGetBudget(string? raw, int expectedSeconds) => WithBudget(raw, () =>
    {
        Assert.Equal(expectedSeconds, LeanCacheProvisioner.DependencyFetchBudget.TotalSeconds);
        Assert.Equal(expectedSeconds, LeanCacheProvisioner.LeanCommandBudget.TotalSeconds);
    });

    private static void WithBudget(string? value, Action action)
    {
        var previous = Environment.GetEnvironmentVariable(BudgetVariable);
        try
        {
            Environment.SetEnvironmentVariable(BudgetVariable, value);
            action();
        }
        finally { Environment.SetEnvironmentVariable(BudgetVariable, previous); }
    }

    private sealed class BudgetRunner : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();
        internal List<TimeSpan> Budgets { get; } = [];
        public ProcessOutput Run(string file, IReadOnlyList<string> args, string root, TimeSpan budget) =>
            inner.Run(file, args, root, budget);
        public ProcessOutput RunWithEnvironment(string file, IReadOnlyList<string> args, string root,
            TimeSpan budget, IReadOnlyDictionary<string, string> environment)
        {
            if (file != "git" && args.FirstOrDefault() != "--version")
                Budgets.Add(budget);
            return inner.RunWithEnvironment(file, args, root, budget, environment);
        }
    }
}
