namespace StrataLint.ArchitectureTests;

public sealed class DefaultInjectionTests
{
    [Fact]
    public void RepositoryPublicDslAndBuildersDoNotInjectCanonicalDefaults()
    {
        Assert.Empty(DefaultInjectionPolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Theory]
    [InlineData("public static class SyntheticDsl", "public static void Create", "D5/S1/Phase/Basic")]
    [InlineData("public sealed class SyntheticBuilder", "public SyntheticBuilder", "D5-T0017")]
    public void CanonicalLiteralDefaultIsRejectedByTheRedFixture(
        string typeDeclaration,
        string memberDeclaration,
        string canonicalValue)
    {
        var source = $$"""
            {{typeDeclaration}}
            {
                {{memberDeclaration}}(string value = "{{canonicalValue}}") { }
            }
            """;

        var finding = Assert.Single(DefaultInjectionPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source));

        Assert.Contains("canonical value", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NonPublicOrNonDslDefaultsAreNotRejected()
    {
        const string source = """
            public static class OrdinaryFactory
            {
                public static void Create(string value = "D5/S1/Phase/Basic") { }
            }

            public static class InternalDsl
            {
                private static void Create(string value = "D5-T0017") { }
            }

            internal static class InternalContainer
            {
                public static class NestedDsl
                {
                    public static void Create(string value = "D5-T0017") { }
                }
            }
            """;

        Assert.Empty(DefaultInjectionPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source));
    }
}
