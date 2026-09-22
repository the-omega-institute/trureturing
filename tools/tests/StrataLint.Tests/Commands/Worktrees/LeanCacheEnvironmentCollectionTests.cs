namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheEnvironmentCollectionTests
{
    [Theory]
    [InlineData(null)]
    [InlineData("/caller/lean/donor")]
    public void DonorFixtureRestoresCallerOverrideAfterFailure(string? callerDonor)
    {
        const string variable = "STRATALINT_LEAN_CACHE_DONORS";
        var previous = Environment.GetEnvironmentVariable(variable);
        try
        {
            Environment.SetEnvironmentVariable(variable, callerDonor);
            Assert.Throws<InvalidOperationException>((Action)(() =>
            {
                using var fixture = new LeanCacheEnsureCommandTests();
                Assert.Null(Environment.GetEnvironmentVariable(variable));
                throw new InvalidOperationException("synthetic test failure");
            }));
            Assert.Equal(callerDonor, Environment.GetEnvironmentVariable(variable));
        }
        finally { Environment.SetEnvironmentVariable(variable, previous); }
    }

    [Fact]
    public void LeanCacheEnvironmentCollectionDoesNotRunBesideProcessStartingTests()
    {
        var definitionType = Assert.Single(
            typeof(WorktreeCommandTests).Assembly.GetTypes(),
            static type =>
                type.CustomAttributes.Any(static attribute =>
                    attribute.AttributeType == typeof(CollectionDefinitionAttribute)
                    && string.Equals(
                        attribute.ConstructorArguments.Single().Value as string,
                        "Lean cache environment",
                        StringComparison.Ordinal)));
        var definition = Assert.IsType<CollectionDefinitionAttribute>(
            Attribute.GetCustomAttribute(
                definitionType,
                typeof(CollectionDefinitionAttribute)));

        Assert.True(definition.DisableParallelization);
    }
}

public sealed partial class LeanCacheEnsureCommandTests : IDisposable
{
    private readonly string? callerDonors = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS");

    // Each synthetic worktree test owns its donor inventory. Individual tests
    // can still set an explicit donor, and xUnit restores the caller on disposal.
    public LeanCacheEnsureCommandTests() => Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS", null);

    public void Dispose() => Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS", callerDonors);
}

[CollectionDefinition("Lean cache environment", DisableParallelization = true)]
public sealed class LeanCacheEnvironmentCollectionDefinition;
