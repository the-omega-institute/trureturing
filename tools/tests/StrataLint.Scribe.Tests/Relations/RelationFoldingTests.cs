namespace StrataLint.Scribe.Tests;

public sealed class RelationFoldingTests
{
    [Fact]
    public void LocalFunctionCaptureCannotReplaceDiscriminantBinding()
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static bool Choice => false;
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                bool flag = false;
                Heading Title() { flag = Choice; return H("title"); }
                var title = Title();
                return new DocumentBlock.Section(title, Blocks(flag ? a : b));
            }
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Fact]
    public void ReadonlyDiscriminantCannotReadLaterFieldInitializer()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(Choice ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))", """
            private static readonly bool Choice = Later;
            private static readonly bool Later = true;
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("ConditionalExpression", read.Failure?.Shape);
    }

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
    [InlineData("System.Linq.Enumerable.Select(Unknown, item => item)")]
    [InlineData("System.Linq.Enumerable.SelectMany(Unknown, item => new[] { item })")]
    [InlineData("System.Linq.Enumerable.ToArray(Unknown)")]
    public void UnknownProjectionSourcesAreRejected(string expression)
    {
        using var root = RelationContractTests.Fixture("new DocumentBlock.Paragraph(InlineSequence.Create(" + expression + "))",
            "private static Inline[] Unknown => new[] { Ref(\"D5/S0/Test/First\") };");
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
    [InlineData("Item(null), Item(\"Second\")", "private static DocumentBlock Item(string? value) => Paragraph(Ref(\"D5/S0/Test/\" + (value switch { null => \"First\", \"Second\" => \"Second\", _ => string.Join(\"/\", new[] { \"unused\" }) }))); ")]
    [InlineData("Item(ResolutionKind.Proved), Item(ResolutionKind.Refuted)", "private static DocumentBlock Item(ResolutionKind value) => Paragraph(Ref(\"D5/S0/Test/\" + (value switch { ResolutionKind.Proved => \"First\", _ => \"Second\" }))); ")]
    [InlineData("Item(true), Item(false)", "private static DocumentBlock Item(bool value) { if (value) { var target = \"D5/S0/Test/First\"; return Paragraph(Ref(target)); } else return Paragraph(Ref(\"D5/S0/Test/Second\")); }")]
    public void HelperCallSitesChooseIndependentBranches(string blocks, string helper)
    {
        using var root = RelationContractTests.Fixture(blocks, helper);
        RelationContractTests.EqualExecution(root, "M:System.String.Join(System.String,System.String[])\n");
        var references = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection!.InlineReferences;
        Assert.Equal(new[] { "D5/S0/Test/First", "D5/S0/Test/Second" }, references);
    }

    [Theory]
    [InlineData("\"First\" ?? string.Join(\"/\", new[] { \"unused\" })")]
    [InlineData("true ? \"First\" : string.Join(\"/\", new[] { \"unused\" })")]
    [InlineData("false ? string.Join(\"/\", new[] { \"unused\" }) : \"First\"")]
    [InlineData("\"First\" switch { \"First\" => \"First\", _ => string.Join(\"/\", new[] { \"unused\" }) }")]
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
                if (value) return Paragraph(Ref(string.Join("/", new[] { "unused" })));
                return Paragraph(Ref("D5/S0/Test/First"));
            }
            """);
        RelationContractTests.EqualExecution(root, "M:System.String.Join(System.String,System.String[])\n");
    }

    [Fact]
    public void UnselectedPresentationEffectsAreNotInspected()
    {
        using var root = RelationContractTests.Fixture("Item(false)", """
            private static DocumentBlock Item(bool value)
            {
                if (value) { string label = "first"; return Paragraph(Text(label += "second")); }
                return Paragraph(Ref("D5/S0/Test/First"));
            }
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Theory]
    [InlineData("name == \"First\" ? name : \"Second\"")]
    [InlineData("name is \"First\" or \"Third\" ? name : \"Second\"")]
    public void ConstantPredicatesChooseBranches(string expression)
    {
        using var root = RelationContractTests.Fixture("Item(\"First\"), Item(\"Second\")",
            "private static DocumentBlock Item(string name) => Paragraph(Ref(\"D5/S0/Test/\" + (" + expression + ")));");
        RelationContractTests.EqualExecution(root);
    }

    [Theory]
    [InlineData("Item(1)", "private static DocumentBlock Item(int value) => Paragraph(Ref(value == 1L ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"));")]
    [InlineData("Item(1L)", "private static DocumentBlock Item(long value) => Paragraph(Ref(value switch { 1 => \"D5/S0/Test/First\", _ => \"D5/S0/Test/Second\" }));")]
    [InlineData("Item(double.NaN)", "private static DocumentBlock Item(double value) => Paragraph(Ref(value == double.NaN ? \"D5/S0/Test/Second\" : \"D5/S0/Test/First\"));")]
    [InlineData("Item(-1)", "private static DocumentBlock Item(int value) => Paragraph(Ref(value == -1 ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"));")]
    public void NumericDiscriminantsRetainCSharpConversions(string blocks, string helper)
    {
        using var root = RelationContractTests.Fixture(blocks, helper);
        RelationContractTests.EqualExecution(root, "T:System.Double\nF:System.Double.NaN\n");
        Assert.Equal("D5/S0/Test/First", Assert.Single(StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection!.InlineReferences));
    }

    [Fact]
    public void CollectionProjectionReadsSelectedLambdaBranches()
    {
        using var root = RelationContractTests.Fixture("Item()", """
            private static DocumentBlock Item()
            {
                string[] names = ["First", "Second"];
                return new DocumentBlock.Paragraph(InlineSequence.Create(System.Linq.Enumerable.Select(names,
                    name => Ref("D5/S0/Test/" + (name == "First" ? "First" : "Second")))));
            }
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void EnumConstantPatternChoosesEachCallSite()
    {
        using var root = RelationContractTests.Fixture("Item(DescribeRole.Definition), Item(DescribeRole.Theorem)", """
            private static DocumentBlock Item(DescribeRole role) => Paragraph(Ref(
                role is DescribeRole.Definition ? "D5/S0/Test/First" : "D5/S0/Test/Second"));
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void MissingParamsIsAnEmptyCollection()
    {
        using var root = RelationContractTests.Fixture("Item()", """
            private static DocumentBlock Item(params DocumentBlock[] extra) =>
                new DocumentBlock.Section(H("section"), Blocks([Paragraph(Ref("D5/S0/Test/First")), .. extra]));
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void PresentationHelpersKeepTheirExistingEffectTraversal()
    {
        using var root = RelationContractTests.Fixture("""
            Describe.Lean(DescribeId.Create("sample"), DeclarationHandle.Create("D5/S0/Test/First.claim"),
                H("sample"), StatementSource.FromAuthor(Display()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Math(Display()))), DescribeRole.Theorem)
            """, """
            private static Formula Display()
            {
                var number = 1;
                number++;
                return Num(number);
            }
            """);
        foreach (var (name, schema) in new[]
        {
            ("statement-projection-pilot-v1.json", "statement-projection-pilot-fixture-v1"),
            ("statement-projection-expansion-v1.json", "statement-projection-expansion-fixture-v1"),
        })
            File.WriteAllText(root.Resolve("Golden/Projection/" + name),
                "{\"schema\":\"" + schema + "\",\"declarations\":[]}");
        RelationContractTests.EqualExecution(root);
    }

    [Theory]
    [InlineData("System.Linq.Enumerable.Select(new[] { \"First\", \"Second\" }, item => Ref(\"D5/S0/Test/\" + item))")]
    [InlineData("System.Linq.Enumerable.ToArray(new[] { Ref(\"D5/S0/Test/First\"), Ref(\"D5/S0/Test/Second\") })")]
    [InlineData("new[] { \"First\", \"Second\" }.Select(item => Ref(\"D5/S0/Test/\" + item)).ToArray()")]
    public void FiniteProjectionMatchesExecution(string expression)
    {
        using var root = RelationContractTests.Fixture("new DocumentBlock.Paragraph(InlineSequence.Create(" + expression + "))");
        RelationContractTests.EqualExecution(root);
        Assert.Equal(2, StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection!.InlineReferences.Length);
    }
}
