using System.Collections.Immutable;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Tests;

public sealed class RelationBoundaryTests
{
    [Theory]
    [InlineData("\"D5/S0/Test/\" + (true ? \"First\" : \"Second\")", "ConditionalExpression")]
    [InlineData("nameof(Relations)", "UnsupportedInvocation")]
    [InlineData("\"D5/S0/Test/First.claim\" + (1 + 2)", "NonStringAddition")]
    [InlineData("\"D5/S0/Test/\" + ResolutionKind.Proved", "NonConstantString")]
    public void NestedUnknownFormsAreNotFoldedAway(string expression, string shape)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(" + expression + "))");
        var result = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(result.Projection);
        Assert.Equal(shape, result.Failure?.Shape);
    }

    [Theory]
    [InlineData("\"D5/S0/Test/First.claim\" + (char)97")]
    [InlineData("\"D5/S0/Test/First.claim\" + ((byte)12)")]
    public void ConstantCastsRetainCSharpSemantics(string expression)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(" + expression + "))");
        AssertMatches(root);
    }

    [Theory]
    [InlineData("Paragraph(Ref(1 switch { 1 => \"D5/S0/Test/First\", _ => \"D5/S0/Test/Second\" }))", "", "SwitchExpression")]
    [InlineData("Paragraph(Ref(Target))", "private static string Target => \"D5/S0/Test/First\";", "UnresolvedSymbol")]
    [InlineData("Paragraph(Ref(Target))", "private static string Target = \"D5/S0/Test/First\";", "MutableField")]
    [InlineData("Item()", "private DocumentBlock Item() => Paragraph(Ref(\"D5/S0/Test/First\"));", "InstanceHelper")]
    [InlineData("Item()", "private static DocumentBlock Item() { if (true) return Paragraph(Ref(\"D5/S0/Test/First\")); return Paragraph(Text(\"content\")); }", "IfStatement")]
    [InlineData("Paragraph(Ref($\"D5/S0/Test/First.claim{1:00}\"))", "", "InterpolationFormat")]
    public void UnsupportedCorpusShapesAreNamed(string blocks, string helper, string shape)
    {
        using var root = RelationContractTests.Fixture(blocks, helper);
        var result = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(result.Projection);
        Assert.Equal(shape, result.Failure?.Shape);
        Assert.True(result.Failure!.Line > 0);
    }

    [Fact]
    public void MutableHelperBodyIsRejected()
    {
        using var root = RelationContractTests.Fixture("Item(\"First\")", """
            private static DocumentBlock Item(string name)
            {
                name = "Second";
                return Paragraph(Ref("D5/S0/Test/" + name));
            }
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Fact]
    public void IgnoredPresentationAssignmentIsRejected()
    {
        using var root = MutationFixture("string target = \"First\"; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(target = \"Second\"), Ref(\"D5/S0/Test/\" + target)))));");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Fact]
    public void IgnoredPresentationLocalInitializerAssignmentIsRejected()
    {
        using var root = MutationFixture("string target = \"First\"; var ignored = target = \"Second\"; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"), Ref(\"D5/S0/Test/\" + target)))));");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Fact]
    public void IgnoredPresentationLocalWriteIsRejected()
    {
        using var root = MutationFixture("string target = \"First\"; string ignored = \"First\"; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(ignored = \"Second\"), Ref(\"D5/S0/Test/\" + target)))));");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Theory]
    [InlineData("target += \"Second\";")]
    [InlineData("target++;")]
    [InlineData("Mutate(out target);")]
    [InlineData("field = \"Second\";")]
    public void IgnoredPresentationWritesAreRejected(string statement)
    {
        using var root = MutationFixture("string target = \"First\"; " + statement + " return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"), Ref(\"D5/S0/Test/\" + target)))));", "private string field = \"First\";\n        private static void Mutate(out string value) { value = \"Second\"; }\n        private static void Unknown(string value) { }");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Fact]
    public void UnknownPresentationCallIsRejected()
    {
        using var root = MutationFixture(
            "string target = \"First\"; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(DateTime.Now.ToString()), Ref(\"D5/S0/Test/\" + target)))));");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Theory]
    [InlineData("string.Join(\",\", new[] { \"a\" })")]
    [InlineData("\"\" + System.Linq.Enumerable.Prepend(new[] { \"a\" }, \"b\")")]
    [InlineData("\"\" + System.Linq.Enumerable.ToList(new[] { \"a\" })")]
    [InlineData("\"\" + System.Linq.Enumerable.Distinct(new[] { \"a\" })")]
    [InlineData("\"\" + System.Linq.Enumerable.OrderBy(new[] { \"a\" }, item => item)")]
    [InlineData("\"\" + System.Linq.Enumerable.ThenBy(System.Linq.Enumerable.OrderBy(new[] { \"a\" }, item => item), item => item)")]
    public void UnsupportedPresentationMembersAreRejected(string expression)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(" + expression + "))");
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Theory]
    [InlineData("Clear()")]
    [InlineData("Remove(1)")]
    [InlineData("RemoveAt(0)")]
    public void UnsupportedPresentationListMutatorsAreRejected(string invocation)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(Label()))", $$"""
            private static string Label()
            {
                var values = new System.Collections.Generic.List<int> { 1 };
                values.{{invocation}};
                return "text";
            }
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    private static TemporaryRoot MutationFixture(string body, string members = "")
    {
        var root = new TemporaryRoot();
        File.WriteAllText(root.Resolve("global.json"), "{}");
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), $$"""
            using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Relations : IScribeDocumentDefinition
            {
                {{members}}
                public DocumentDefinition Create() { {{body}} }
            }
            """);
        return root;
    }

    [Fact]
    public void StaticReadingDoesNotExecutePresentationHelpers()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        var source = File.ReadAllText(root.Resolve(RelationContractTests.Entry));
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), source.Replace("H(\"title\")", "Title()", StringComparison.Ordinal)
            .Replace("public DocumentDefinition Create()", "private static Heading Title() => throw new InvalidOperationException(\"title\");\n    public DocumentDefinition Create()", StringComparison.Ordinal));
        Assert.NotNull(StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry).Projection);
        Assert.Equal(ScribeScriptFailureCode.CreateFailed, ScribeScriptHost.Execute(root.Path, RelationContractTests.Entry).Failure?.Code);
    }

    [Fact]
    public void ConstructorsCannotReplaceReadonlyRelationInitializers()
    {
        using var root = RelationContractTests.Fixture("item", """
            private readonly DocumentBlock item = Paragraph(Ref("D5/S0/Test/First"));
            public Relations() { item = Paragraph(Ref("D5/S0/Test/Second")); }
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("ConstructorState", read.Failure?.Shape);
    }

    [Fact]
    public void PresentationHelpersCannotMutateRelations()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), """
            using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Relations : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
                    DocumentBlock[] items = [Paragraph(Ref("D5/S0/Test/First"))];
                    return DocumentDefinition.Create(ScribeNode.Create("digest", Title(items), Blocks(items)));
                }
                private static Heading Title(DocumentBlock[] items)
                {
                    items[0] = Paragraph(Ref("D5/S0/Test/Second"));
                    return H("title");
                }
            }
            """);
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal("IgnoredWrite", read.Failure?.Shape);
    }

    [Theory]
    [InlineData(8, true)]
    [InlineData(9, false)]
    public void HelperDepthHasAnExplicitBoundary(int depth, bool readable)
    {
        var helpers = string.Join("\n", Enumerable.Range(0, depth).Select(index =>
            $"private static DocumentBlock Item{index}() => "
            + (index == depth - 1 ? "Paragraph(Ref(\"D5/S0/Test/First\"));" : $"Item{index + 1}();")));
        using var root = RelationContractTests.Fixture("Item0()", helpers);
        var result = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Equal(readable, result.Projection is not null);
        if (!readable) Assert.Equal("HelperDepth", result.Failure?.Shape);
    }

    [Fact]
    public void ParamsHelpersAndLocalInitializersPreserveRelations()
    {
        using var root = RelationContractTests.Fixture("Items(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static DocumentBlock Items(params DocumentBlock[] children)
            {
                var content = Blocks(children);
                return new DocumentBlock.Section(H("section"), content);
            }
            """);
        AssertMatches(root);
    }

    [Fact]
    public void ArraySpreadAndDirectAstConstructionPreserveRelations()
    {
        using var root = RelationContractTests.Fixture("""
            new DocumentBlock.Section(H("section"), BlockSequence.Create(
                [.. new DocumentBlock[] { new DocumentBlock.Paragraph(InlineSequence.Create(
                    [new Inline.GidReference(GidRef.Create("D5/S0/Test/First"))])) }]))
            """);
        AssertMatches(root);
    }

    [Fact]
    public void LocalFunctionDeclarationsDoNotExecuteAndStaticTemplatesExpand()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        File.WriteAllText(root.Resolve(RelationContractTests.Entry), """
            using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Relations : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
                    Formula Display() => Id("x");
                    static DocumentBlock Item(string name) => Paragraph(Ref("D5/S0/Test/" + name));
                    return DocumentDefinition.Create(ScribeNode.Create("digest", H("title"),
                        Blocks(Item("First"), Paragraph(Math(Display())))));
                }
            }
            """);
        AssertMatches(root);
    }

    [Theory]
    [InlineData("DeclarationHandle.Create(\"D5/S0/Test/First.claim\").Value", "")]
    [InlineData("LibraryNoteRef.Create(\"D5/L/sample2000note\").Value", "")]
    [InlineData("Target.Value", "private static readonly DeclarationHandle Target = DeclarationHandle.Create(\"D5/S0/Test/First.claim\");")]
    public void TypedValueSelectorsPreserveCanonicalTargets(string expression, string field)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(" + expression + "))", field);
        AssertMatches(root);
    }

    [Fact]
    public void PresentationArrayMutationCannotAlterRelations()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(\"D5/S0/Test/First\"))", """
            private static Heading Title()
            {
                Formula[] values = [Num(1)];
                values[0] = Num(2);
                return H("title");
            }
            """);
        File.WriteAllText(root.Resolve(RelationContractTests.Entry),
            File.ReadAllText(root.Resolve(RelationContractTests.Entry)).Replace("H(\"title\"), Blocks", "Title(), Blocks", StringComparison.Ordinal));
        AssertMatches(root);
    }

    [Fact]
    public void ClaimsIncludeHostAndEveryAdditionalMember()
    {
        using var root = RelationContractTests.Fixture("""
            Describe.Lean(DescribeId.Create("resolution"), DeclarationHandle.Create("D5/S0/Test/First.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("content"))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("sample-problem"), ResolutionKind.Refuted,
                    [DeclarationHandle.Create("D5/S0/Test/Second.claim"), DeclarationHandle.Create("D5/S0/Test/Third.claim")]))
            """);
        foreach (var (name, schema) in new[]
        {
            ("statement-projection-pilot-v1.json", "statement-projection-pilot-fixture-v1"),
            ("statement-projection-expansion-v1.json", "statement-projection-expansion-fixture-v1"),
        })
            File.WriteAllText(root.Resolve("Golden/Projection/" + name),
                "{\"schema\":\"" + schema + "\",\"declarations\":[]}");
        var projection = AssertMatches(root);
        var describe = Assert.Single(projection.Describes);
        Assert.Equal("report-derived", describe.KindSource);
        Assert.Equal("Theorem", describe.Role);
        Assert.Equal("Theorem", describe.Kind);
        Assert.NotNull(describe.Claim);
        Assert.Equal("sample-problem", describe.Claim.Problem);
        Assert.Equal("Refuted", describe.Claim.Resolution);
        Assert.Equal(new[] { "D5/S0/Test/First.claim", "D5/S0/Test/Second.claim", "D5/S0/Test/Third.claim" }, describe.Claim.Members);
    }

    [Fact]
    public void ComparisonReportsMismatchPathAndFirstDifference()
    {
        const string path = RelationContractTests.Entry;
        var definition = DocumentDefinition.Create(
            ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Ref("D5/S0/Test/First"))), sourcePath: path),
            sourcePath: path);
        var wrong = RelationProjection.FromDefinition(definition) with { InlineReferences = ["D5/S0/Test/Second"] };
        var result = RelationVerifier.Compare([new(path, wrong, null)], [new(path, definition, null)], TimeSpan.Zero);
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, result.Write(output, error));
        Assert.Equal(1, result.Mismatches);
        Assert.Contains(path, error.ToString(), StringComparison.Ordinal);
        Assert.Contains("static=inline:", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("Second", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("First", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void HostFailureIsCountedAndNamed()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        File.AppendAllText(root.Resolve(RelationContractTests.Entry), "\ninvalid tokens\n");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, ScribeCli.Run(typeof(RelationBoundaryTests).Assembly, ["relations", "verify"],
            root.Path, output, error, TextReader.Null));
        Assert.Contains("hostFailures=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("Compilation", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("../Outside.scribe.cs")]
    [InlineData("Blueprint/D5/S0/Test/Missing.scribe.cs")]
    [InlineData("")]
    public void InvalidSelectionsAreInputErrors(string selected)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        Assert.Equal(2, ScribeCli.Run(typeof(RelationBoundaryTests).Assembly, ["relations", "verify", "--paths-from", "-"],
            root.Path, TextWriter.Null, new StringWriter(), new StringReader(selected)));
    }

    [Fact]
    public void SelectionFilesDeduplicateAndExcludeUnselectedDefinitions()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Text(\"content\"))");
        const string other = "Blueprint/D5/S0/Test/Other.scribe.cs";
        File.WriteAllText(root.Resolve(other), File.ReadAllText(root.Resolve(RelationContractTests.Entry))
            .Replace("Paragraph(Text(\"content\"))", "Paragraph(Ref(true ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))", StringComparison.Ordinal));
        var selection = root.Resolve("selection.txt");
        File.WriteAllText(selection, RelationContractTests.Entry + "\n" + RelationContractTests.Entry);
        var output = new StringWriter();
        Assert.Equal(0, ScribeCli.Run(typeof(RelationBoundaryTests).Assembly,
            ["relations", "verify", "--paths-from", selection], root.Path, output, new StringWriter(), TextReader.Null));
        Assert.Contains("paths=1 unreadable=0", output.ToString(), StringComparison.Ordinal);
        output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, ScribeCli.Run(typeof(RelationBoundaryTests).Assembly,
            ["relations", "verify"], root.Path, output, error, TextReader.Null));
        Assert.Contains("paths=2 unreadable=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains(other, error.ToString(), StringComparison.Ordinal);
    }

    private static RelationProjection AssertMatches(TemporaryRoot root)
    {
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Failure);
        RelationContractTests.EqualExecution(root);
        return read.Projection!;
    }
}
