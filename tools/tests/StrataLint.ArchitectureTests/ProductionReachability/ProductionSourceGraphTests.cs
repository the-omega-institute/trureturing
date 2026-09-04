namespace StrataLint.ArchitectureTests;

public sealed class ProductionSourceGraphTests
{
    private const string TargetPath = "tools/Synthetic/TargetType.cs";
    private const string NamespaceDeclaration = "name" + "space Synthetic;\n";
    private const string TargetSource = NamespaceDeclaration
        + "internal static class TargetType\n"
        + "{\n"
        + "    internal static bool Target(int value) => value > 0;\n"
        + "}\n";

    [Fact]
    public void ProductionReferencePathsIncludesMethodGroupReference()
    {
        const string consumerPath = "tools/Synthetic/MethodGroupConsumer.cs";
        var graph = GraphWith(
            consumerPath,
            NamespaceDeclaration
                + "internal delegate bool SomeDelegate(int value);\n"
                + "internal static class MethodGroupConsumer\n"
                + "{\n"
                + "    internal static SomeDelegate Resolve() =>\n"
                + "        (SomeDelegate)TargetType.Target;\n"
                + "}\n");

        Assert.Contains(consumerPath, ReferencesToTarget(graph));
    }

    [Fact]
    public void ProductionReferencePathsIgnoresCommentsAndStrings()
    {
        const string consumerPath = "tools/Synthetic/LexicalOnlyConsumer.cs";
        var graph = GraphWith(
            consumerPath,
            NamespaceDeclaration
                + "internal static class LexicalOnlyConsumer\n"
                + "{\n"
                + "    // TargetType.Target\n"
                + "    internal const string Text = \"TargetType.Target\";\n"
                + "}\n");

        Assert.DoesNotContain(consumerPath, ReferencesToTarget(graph));
    }

    [Fact]
    public void ProductionReferencePathsIncludesInvocation()
    {
        const string consumerPath = "tools/Synthetic/InvocationConsumer.cs";
        var graph = GraphWith(
            consumerPath,
            NamespaceDeclaration
                + "internal static class InvocationConsumer\n"
                + "{\n"
                + "    internal static bool Resolve() => TargetType.Target(1);\n"
                + "}\n");

        Assert.Contains(consumerPath, ReferencesToTarget(graph));
    }

    private static ProductionSourceGraph GraphWith(string consumerPath, string consumerSource) =>
        ProductionSourceGraph.FromSources(
        [
            (TargetPath, TargetSource),
            (consumerPath, consumerSource),
        ]);

    private static IReadOnlyList<string> ReferencesToTarget(ProductionSourceGraph graph)
    {
        var target = Assert.Single(graph.MethodDefinitionsNamed("Target"));
        return graph.ProductionReferencePaths(target);
    }
}
