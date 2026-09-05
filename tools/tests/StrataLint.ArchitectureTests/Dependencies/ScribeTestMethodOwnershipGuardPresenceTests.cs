using System.Reflection;

namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMethodOwnershipGuardPresenceTests
{
    [Fact]
    public void SymbolLevelOwnershipRuleIsPresentAndExecutable()
    {
        const string typeName =
            "StrataLint.ArchitectureTests.ScribeTestMethodOwnershipTests";
        const string methodName =
            "EveryScribeTestMethodBelongsToItsSymbolLevelProductionOwner";

        var guardType = typeof(ScribeTestMethodOwnershipGuardPresenceTests)
            .Assembly
            .GetType(typeName, throwOnError: false);
        var guard = guardType?.GetMethod(
            methodName,
            BindingFlags.Public | BindingFlags.Instance);

        Assert.NotNull(guardType);
        Assert.NotNull(guard);
        var fact = guard!.GetCustomAttributes<FactAttribute>(inherit: false).SingleOrDefault();
        Assert.NotNull(fact);
        Assert.Null(fact!.Skip);
    }
}
