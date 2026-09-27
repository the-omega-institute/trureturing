using System.Reflection;

namespace StrataLint.Engine.Tests;

public sealed class BoundedProcessRunnerBudgetTests
{
    [Fact]
    public void HangDetectionBudgetIsFiniteAndPositive()
    {
        var field = typeof(BoundedProcessRunner).GetField(
            "HangDetectionBudget",
            BindingFlags.NonPublic | BindingFlags.Static);

        Assert.NotNull(field);
        var budget = Assert.IsType<TimeSpan>(field.GetValue(null));
        Assert.True(budget > TestBudgets.ZeroDuration);
        Assert.NotEqual(Timeout.InfiniteTimeSpan, budget);
    }
}
