namespace StrataLint.Tests;

public sealed class LeanCacheEnvironmentCollectionTests
{
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

[CollectionDefinition("Lean cache environment", DisableParallelization = true)]
public sealed class LeanCacheEnvironmentCollectionDefinition;
