using System.Reflection;
using System.Text;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Tests;

public sealed class RelationContractTests
{
    internal const string Entry = "Blueprint/D5/S0/Test/Relations.scribe.cs";

    [Theory]
    [InlineData("true ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"", "ConditionalExpression")]
    [InlineData("new[] { \"D5/S0/Test/First\" }[0]", "ElementAccessExpression")]
    [InlineData("string.Join(\"/\", \"D5\", \"S0\", \"Test\", \"First\")", "UnsupportedInvocation")]
    public void UnknownRelationExpressionsFailClosed(string expression, string shape)
    {
        using var root = Fixture("Paragraph(Ref(" + expression + "))");
        var result = Read(root);
        Assert.Null(Property(result, "Projection"));
        var failure = Property(result, "Failure");
        Assert.NotNull(failure);
        Assert.Equal(shape, Property(failure, "Shape"));
        Assert.Equal(Entry, Property(failure, "SourcePath"));
        Assert.True((int)Property(failure, "Line")! > 0);
    }

    [Fact]
    public void RecursiveHelpersFailClosed()
    {
        using var root = Fixture("Cycle()", "private static DocumentBlock Cycle() => Cycle();");
        Assert.Equal("RecursiveHelper", Property(Property(Read(root), "Failure")!, "Shape"));
    }

    [Theory]
    [InlineData("\"D5/S0/Test/First\"", "")]
    [InlineData("Target", "private const string Target = \"D5/S0/Test/First\";")]
    [InlineData("\"D5/S0/\" + \"Test/First\"", "")]
    [InlineData("$\"D5/S0/Test/{\"First\"}\"", "")]
    [InlineData("\"D5/S0/Test/FIRST\".Replace(\"FIRST\", \"First\")", "")]
    [InlineData("\"D5/S0/Test/First\".Replace('x', 'y')", "")]
    [InlineData("\"D5/S0/Test/\" + \"FIRST\".ToLowerInvariant()", "")]
    [InlineData("\"D5/S0/Test/\" + \"first\".ToUpperInvariant()", "")]
    [InlineData("\" D5/S0/Test/First \".Trim()", "")]
    [InlineData("Target(\"First\")", "private static string Target(string name) => \"D5/S0/Test/\" + name;")]
    public void ConstantFormsMatchExecution(string expression, string helper)
    {
        using var root = Fixture("Paragraph(Ref(" + expression + "))", helper);
        EqualExecution(root);
    }

    [Fact]
    public void HelperCallSitesPreserveMultiplicity()
    {
        using var root = Fixture("Item(\"First\"), Item(\"First\")",
            "private static DocumentBlock Item(string name) => Paragraph(Ref(\"D5/S0/Test/\" + name));");
        var encoded = EqualExecution(root);
        Assert.Equal(2, encoded.Split("D5/S0/Test/First", StringSplitOptions.None).Length - 1);
    }

    [Fact]
    public void SharedSourceHelpersAreExpanded()
    {
        using var root = Fixture("Shared.Item(\"First\")", attributes:
            "[ScribeSharedSource(\"Blueprint/D5/S0/Test/Shared.scribe.cs\")]");
        File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Shared.scribe.cs"), """
            using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl;
            internal static class Shared
            {
                internal static DocumentBlock Item(string name) => Paragraph(Ref("D5/S0/Test/" + name));
            }
            """);
        EqualExecution(root);
    }

    [Fact]
    public void ProjectionCoversTypedEdgesDescribesAndNestedReferences()
    {
        using var root = Fixture("""
            new DocumentBlock.Section(H("section"), Blocks(
                Describe.Remark(DescribeId.Create("subject"),
                    DeclarationHandle.Create("D5/S0/Test/First.claim"), H("subject"),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Ref("D5/S0/Test/First"))))))
            """, edges: """
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/First")),
             DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create("D5/S0/Test/First.claim")),
             DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/Second")),
             DocumentEdge.NarrativeReference.ToDescribe(GidRef.Create("D5/S0/Test/Second"), DescribeId.Create("subject"))]
            """);
        var encoded = EqualExecution(root);
        foreach (var value in new[] { "dependency", "truth", "narrative", "subject", "Remark", "First.claim" })
            Assert.Contains(value, encoded, StringComparison.Ordinal);
    }

    [Fact]
    public void ProjectionIsDeterministicAndIgnoresMultisetOrder()
    {
        var first = Definition(Blocks(Paragraph(Ref("D5/S0/Test/First")), Paragraph(Ref("D5/S0/Test/Second"))));
        var second = Definition(Blocks(Paragraph(Ref("D5/S0/Test/Second")), Paragraph(Ref("D5/S0/Test/First"))));
        Assert.Equal(Encode(Project(first)), Encode(Project(first)));
        Assert.Equal(Encode(Project(first)), Encode(Project(second)));
        Assert.NotEqual(Encode(Project(first)), Encode(Project(Definition(Blocks(Paragraph(Ref("D5/S0/Test/First")))))));
    }

    [Fact]
    public void RelationsVerifyAcceptsEquivalentSyntheticSet()
    {
        using var root = Fixture("Paragraph(Ref(\"D5/S0/Test/First\"))");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, Run(root, output, error));
        Assert.Contains("paths=1 unreadable=0 hostFailures=0 mismatches=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void RelationsVerifyNamesUnreadableShape()
    {
        using var root = Fixture("Paragraph(Ref(true ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, Run(root, output, error));
        Assert.Contains("ConditionalExpression", error.ToString(), StringComparison.Ordinal);
        Assert.Contains(Entry, error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("relations")]
    [InlineData("relations", "other")]
    [InlineData("relations", "verify", "--bad")]
    [InlineData("relations", "verify", "--paths-from", "")]
    public void RelationsVerifyRejectsInvalidArguments(params string[] args)
    {
        using var root = Fixture("Paragraph(Text(\"content\"))");
        Assert.Equal(2, ScribeCli.Run(typeof(RelationContractTests).Assembly, args,
            root.Path, TextWriter.Null, new StringWriter(), TextReader.Null));
    }

    internal static TemporaryRoot Fixture(string blocks, string helper = "", string attributes = "", string edges = "null")
    {
        var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}");
        File.WriteAllText(root.Resolve(Entry), $$"""
            using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl;
            {{attributes}}
            internal sealed class Relations : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks({{blocks}}), edges: {{edges}}));
                {{helper}}
            }
            """);
        return root;
    }

    private static int Run(TemporaryRoot root, TextWriter output, TextWriter error) => ScribeCli.Run(
        typeof(RelationContractTests).Assembly, ["relations", "verify", "--paths-from", "-"],
        root.Path, output, error, new StringReader(Entry));

    private static string EqualExecution(TemporaryRoot root)
    {
        var read = Read(root);
        Assert.Null(Property(read, "Failure"));
        var host = ScribeScriptHost.Execute(root.Path, Entry);
        Assert.True(host.IsSuccess, host.Failure?.ToString());
        var bytes = Encode(Property(read, "Projection")!);
        Assert.Equal(Encode(Project(host.Definition!)), bytes);
        return Encoding.UTF8.GetString(bytes);
    }

    private static DocumentDefinition Definition(BlockSequence blocks) => DocumentDefinition.Create(
        ScribeNode.Create("digest", H("title"), blocks, sourcePath: Entry), sourcePath: Entry);

    private static object Read(TemporaryRoot root) => Invoke("StaticRelationIndexer", "Read", root.Path, Entry);
    private static object Project(DocumentDefinition definition) => Invoke("RelationProjection", "FromDefinition", definition);
    private static byte[] Encode(object projection) => (byte[])projection.GetType().GetMethod("Encode")!.Invoke(projection, null)!;
    private static object? Property(object value, string name) => value.GetType().GetProperty(name)!.GetValue(value);
    private static object Invoke(string type, string method, params object[] args)
    {
        var target = typeof(ScribeCli).Assembly.GetType("StrataLint.Scribe." + type);
        Assert.NotNull(target);
        return target.GetMethod(method)!.Invoke(null, args)!;
    }
}
