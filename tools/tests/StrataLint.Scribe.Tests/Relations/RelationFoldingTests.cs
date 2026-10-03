namespace StrataLint.Scribe.Tests;

public sealed class RelationFoldingTests
{
    [Theory]
    [InlineData("Unknown ?? \"First\"", "CoalesceExpression")]
    [InlineData("Choice ? \"First\" : \"Second\"", "ConditionalExpression")]
    [InlineData("Unknown switch { null => \"First\", _ => \"Second\" }", "SwitchExpression")]
    public void UnknownDiscriminantsRetainShape(string expression, string shape)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(\"D5/S0/Test/\" + (" + expression + ")))",
            "private static string Unknown => \"First\"; private static bool Choice => true;");
        Assert.Equal(shape, StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Failure?.Shape);
    }

    [Fact]
    public void UnknownIfDiscriminantRetainsShape()
    {
        using var root = RelationContractTests.Fixture("Item()", """
            private static bool Choice => true;
            private static DocumentBlock Item()
            {
                if (Choice) return Paragraph(Ref("D5/S0/Test/First"));
                else return Paragraph(Ref("D5/S0/Test/Second"));
            }
            """);
        Assert.Equal("IfStatement", StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Failure?.Shape);
    }

    [Theory]
    [InlineData("System.Linq.Enumerable.Select(Unknown, item => Ref(item))")]
    [InlineData("System.Linq.Enumerable.SelectMany(Unknown, item => new[] { Ref(item) })")]
    [InlineData("System.Linq.Enumerable.ToArray(Unknown)")]
    public void UnknownProjectionSourcesAreRejected(string expression)
    {
        using var root = RelationContractTests.Fixture("Paragraph(" + expression + ")",
            "private static string[] Unknown => new[] { \"D5/S0/Test/First\" };");
        Assert.Equal("UnsupportedInvocation", StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Failure?.Shape);
    }

    [Fact]
    public void ProjectionLambdaBodyIsChecked()
    {
        using var root = RelationContractTests.Fixture("Paragraph(System.Linq.Enumerable.ToArray(System.Linq.Enumerable.Select(new[] { \"First\" }, item => Ref(string.Join(\"/\", \"D5/S0/Test\", item)))))");
        Assert.Equal("UnsupportedInvocation", StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Failure?.Shape);
    }

    [Theory]
    [InlineData("Item(null), Item(\"Second\")", "private static DocumentBlock Item(string? value) => Paragraph(Ref(\"D5/S0/Test/\" + (value ?? \"First\"))); ")]
    [InlineData("Item(true), Item(false)", "private static DocumentBlock Item(bool value) => Paragraph(Ref(\"D5/S0/Test/\" + (value ? \"First\" : \"Second\"))); ")]
    [InlineData("Item(1), Item(2)", "private static DocumentBlock Item(int value) => Paragraph(Ref(\"D5/S0/Test/\" + (value switch { 1 => \"First\", _ => \"Second\" }))); ")]
    [InlineData("Item(null), Item(\"Second\")", "private static DocumentBlock Item(string? value) => Paragraph(Ref(\"D5/S0/Test/\" + (value switch { null => \"First\", \"Second\" => \"Second\", _ => string.Join(\"/\", \"unused\") }))); ")]
    [InlineData("Item(ResolutionKind.Proved), Item(ResolutionKind.Refuted)", "private static DocumentBlock Item(ResolutionKind value) => Paragraph(Ref(\"D5/S0/Test/\" + (value switch { ResolutionKind.Proved => \"First\", _ => \"Second\" }))); ")]
    [InlineData("Item(true), Item(false)", "private static DocumentBlock Item(bool value) { if (value) { var target = \"D5/S0/Test/First\"; return Paragraph(Ref(target)); } else return Paragraph(Ref(\"D5/S0/Test/Second\")); }")]
    public void HelperCallSitesChooseIndependentBranches(string blocks, string helper)
    {
        using var root = RelationContractTests.Fixture(blocks, helper);
        RelationContractTests.EqualExecution(root);
        var references = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection!.InlineReferences;
        Assert.Equal(new[] { "D5/S0/Test/First", "D5/S0/Test/Second" }, references);
    }

    [Theory]
    [InlineData("\"First\" ?? string.Join(\"/\", \"unused\")")]
    [InlineData("true ? \"First\" : string.Join(\"/\", \"unused\")")]
    [InlineData("false ? string.Join(\"/\", \"unused\") : \"First\"")]
    [InlineData("\"First\" switch { \"First\" => \"First\", _ => string.Join(\"/\", \"unused\") }")]
    public void UnselectedExpressionsAreNotRead(string expression)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(\"D5/S0/Test/\" + (" + expression + ")))");
        RelationContractTests.EqualExecution(root, "M:System.String.Join(System.String,System.String[])\n");
    }

    [Fact]
    public void UnselectedIfBodyIsNotRead()
    {
        using var root = RelationContractTests.Fixture("Item(false)", """
            private static DocumentBlock Item(bool value)
            {
                if (value) return Paragraph(Ref(string.Join("/", "unused")));
                return Paragraph(Ref("D5/S0/Test/First"));
            }
            """);
        RelationContractTests.EqualExecution(root, "M:System.String.Join(System.String,System.String[])\n");
    }

    [Theory]
    [InlineData("System.Linq.Enumerable.Select(new[] { \"First\", \"Second\" }, item => Ref(\"D5/S0/Test/\" + item))")]
    [InlineData("System.Linq.Enumerable.SelectMany(new[] { \"First\", \"Second\" }, item => new[] { Ref(\"D5/S0/Test/\" + item) })")]
    [InlineData("System.Linq.Enumerable.ToArray(new[] { Ref(\"D5/S0/Test/First\"), Ref(\"D5/S0/Test/Second\") })")]
    public void FiniteProjectionMatchesExecution(string expression)
    {
        using var root = RelationContractTests.Fixture("new DocumentBlock.Paragraph(InlineSequence.Create(" + expression + "))");
        RelationContractTests.EqualExecution(root);
        Assert.Equal(2, StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection!.InlineReferences.Length);
    }
}
