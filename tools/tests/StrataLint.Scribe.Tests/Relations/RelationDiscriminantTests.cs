namespace StrataLint.Scribe.Tests;

public sealed class RelationDiscriminantTests
{
    [Fact]
    public void NonNullFactoryContentsDoNotDetermineCoalesceSelection()
    {
        using var root = RelationContractTests.Fixture("Item(AssessedProvenance.FromLiterature(Source))", """
            private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/sample2000source");
            private static DocumentBlock Item(AssessedProvenance? provenance) => Describe.Remark(
                DescribeId.Create("sample"), DeclarationHandle.Create("D5/S0/Test/First.claim"), H("sample"),
                provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Ref("D5/S0/Test/First"))));
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void PresentationLoopDiscriminantsRemainReadable()
    {
        using var root = RelationContractTests.Fixture("""
            Describe.Lean(DescribeId.Create("sample"), DeclarationHandle.Create("D5/S0/Test/First.claim"),
                H("sample"), StatementSource.FromAuthor(Display()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Ref("D5/S0/Test/First"))), DescribeRole.Theorem)
            """, """
            private static Formula Display()
            {
                var items = new System.Collections.Generic.List<Formula>();
                for (var index = 0; index < 3; index++)
                {
                    if (index > 0) items.Add(Num(index));
                }
                return FormulaDsl.Seq(items.ToArray());
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
    [InlineData("if (flag) return H(\"first\"); return H(\"second\");")]
    [InlineData("return flag ? H(\"first\") : H(\"second\");")]
    [InlineData("return flag switch { true => H(\"first\"), _ => H(\"second\") };")]
    public void PresentationOnlyBranchWritesRemainReadable(string result)
    {
        using var root = RelationContractTests.Fixture("new DocumentBlock.Section(Title(), Blocks(Paragraph(Ref(\"D5/S0/Test/First\"))))", $$"""
            private static Heading Title()
            {
                bool flag = false;
                flag = true;
                {{result}}
            }
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void PresentationOnlyFieldDependenciesRemainReadable()
    {
        using var root = RelationContractTests.Fixture("new DocumentBlock.Section(Title(), Blocks(Paragraph(Ref(\"D5/S0/Test/First\"))))", """
            private static readonly bool Choice = Later;
            private static readonly bool Later = true;
            private static Heading Title() => Choice ? H("first") : H("second");
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Theory]
    [InlineData("bool flag = false;", "flag = Choice;", "flag ? a : b")]
    [InlineData("string? flag = null;", "flag = Unknown;", "Paragraph(Ref(\"D5/S0/Test/\" + (flag ?? \"First\")))")]
    [InlineData("int flag = 1;", "flag++;", "flag switch { 1 => a, _ => b }")]
    [InlineData("int flag = 1;", "++flag;", "flag switch { 1 => a, _ => b }")]
    [InlineData("bool flag = false;", "flag |= Choice;", "flag ? a : b")]
    public void LambdaCaptureWritesInvalidateDiscriminants(string declaration, string write, string branch)
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", $$"""
            private static bool Choice => true;
            private static string Unknown => "Second";
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                {{declaration}}
                System.Action change = () => { {{write}} };
                return new DocumentBlock.Section(H("title"), Blocks({{branch}}));
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Theory]
    [InlineData("ref", "flag = true;")]
    [InlineData("out", "flag = true;")]
    public void ByReferenceDiscriminantArgumentsAreRejected(string modifier, string write)
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", $$"""
            private static Heading Title({{modifier}} bool flag) { {{write}} return H("title"); }
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                bool flag = false;
                var title = Title({{modifier}} flag);
                return new DocumentBlock.Section(title, Blocks(flag ? a : b));
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Theory]
    [InlineData("return new DocumentBlock.Section(title, Blocks(flag ? a : b));")]
    [InlineData("if (flag) return new DocumentBlock.Section(title, Blocks(a)); return b;")]
    public void CapturedParameterAssignmentsAreRejected(string result)
    {
        using var root = RelationContractTests.Fixture("Item(false, Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", $$"""
            private static bool Choice => true;
            private static DocumentBlock Item(bool flag, DocumentBlock a, DocumentBlock b)
            {
                Heading Title() { flag = Choice; return H("title"); }
                var title = Title();
                {{result}}
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Theory]
    [InlineData("flag = true;", "ExpressionStatement")]
    [InlineData("if (flag) flag = true;", "IgnoredWrite")]
    [InlineData("Heading Title() { flag = true; return H(\"title\"); }", "IgnoredWrite")]
    public void AllHelperDiscriminantWritesAreRejected(string write, string shape)
    {
        using var root = RelationContractTests.Fixture("Item(false, Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", $$"""
            private static DocumentBlock Item(bool flag, DocumentBlock a, DocumentBlock b)
            {
                {{write}}
                return new DocumentBlock.Section(H("title"), Blocks(flag ? a : b));
            }
            """);
        Rejected(root, shape);
    }

    [Fact]
    public void UnusedHelperArgumentWritesRemainPresentationOnly()
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static DocumentBlock Select(bool unused, bool choice, DocumentBlock a, DocumentBlock b) => choice ? a : b;
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                bool flag = false;
                Heading Title() { flag = true; return H("title"); }
                var title = Title();
                return new DocumentBlock.Section(title, Blocks(Select(flag, true, a, b)));
            }
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Fact]
    public void DiscriminantInitializerDependenciesAreSingleAssignment()
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                bool flag = false;
                bool decision = flag;
                System.Action change = () => { flag = true; };
                return new DocumentBlock.Section(H("title"), Blocks(decision ? a : b));
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Fact]
    public void HelperDiscriminantArgumentsRequireSingleAssignment()
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static DocumentBlock Select(bool choice, DocumentBlock a, DocumentBlock b) => choice ? a : b;
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b)
            {
                bool flag = false;
                System.Action change = () => { flag = true; };
                return new DocumentBlock.Section(H("title"), Blocks(Select(flag, a, b)));
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Fact]
    public void HelperReturnDiscriminantDependenciesRequireSingleAssignment()
    {
        using var root = RelationContractTests.Fixture("Item(Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static bool Select(bool flag)
            {
                Heading Title() { flag = true; return H("title"); }
                var title = Title();
                return flag;
            }
            private static DocumentBlock Item(DocumentBlock a, DocumentBlock b) =>
                new DocumentBlock.Section(H("title"), Blocks(Select(false) ? a : b));
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Fact]
    public void ProjectedDiscriminantsRetainSourceDependencies()
    {
        using var root = RelationContractTests.Fixture("Item()", """
            private static DocumentBlock Item()
            {
                bool choice = false;
                Heading Title() { choice = true; return H("title"); }
                var title = Title();
                bool[] choices = [choice];
                return new DocumentBlock.Section(title, Blocks(new DocumentBlock.Paragraph(InlineSequence.Create(
                    System.Linq.Enumerable.Select(choices,
                        flag => Ref(flag ? "D5/S0/Test/First" : "D5/S0/Test/Second"))))));
            }
            """);
        Rejected(root, "IgnoredWrite");
    }

    [Fact]
    public void SameNamedPresentationLocalDoesNotWriteDiscriminantParameter()
    {
        using var root = RelationContractTests.Fixture("Item(true, Paragraph(Ref(\"D5/S0/Test/First\")), Paragraph(Ref(\"D5/S0/Test/Second\")))", """
            private static Heading Title()
            {
                string flag = "title";
                flag += " text";
                return H(flag);
            }
            private static DocumentBlock Item(bool flag, DocumentBlock a, DocumentBlock b) =>
                new DocumentBlock.Section(Title(), Blocks(flag ? a : b));
            """);
        RelationContractTests.EqualExecution(root);
    }

    [Theory]
    [InlineData("true")]
    [InlineData("(true)")]
    [InlineData("(bool)true")]
    public void ReadonlyConstantDiscriminantsRemainReadable(string initializer)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(Choice ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))",
            "private static readonly bool Choice = " + initializer + ";");
        RelationContractTests.EqualExecution(root);
        Assert.Equal("D5/S0/Test/First", Assert.Single(StaticRelationIndexer.Read(root.Path,
            RelationContractTests.Entry).Projection!.InlineReferences));
    }

    [Theory]
    [InlineData("private static readonly bool Other = true; private static readonly bool Choice = Other;")]
    [InlineData("private static readonly bool Choice = Other; private static bool Other => true;")]
    [InlineData("private readonly bool Choice = true;")]
    [InlineData("private static bool Choice = true;")]
    [InlineData("private static bool Choice => true;")]
    public void FieldAndPropertyDependenciesRetainConditionalShape(string fields)
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(Choice ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))", fields);
        Rejected(root, "ConditionalExpression");
    }

    [Fact]
    public void ReadonlyDiscriminantCannotReferenceConstFieldInitializer()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(Choice ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))",
            "private static readonly bool Choice = Other; private const bool Other = true;");
        Rejected(root, "ConditionalExpression");
    }

    [Theory]
    [InlineData("Paragraph(Ref(Choice ?? \"D5/S0/Test/First\"))", "CoalesceExpression")]
    [InlineData("Paragraph(Ref(Choice switch { null => \"D5/S0/Test/First\", _ => \"D5/S0/Test/Second\" }))", "SwitchExpression")]
    public void ReadonlyFieldDependenciesRetainBranchShape(string block, string shape)
    {
        using var root = RelationContractTests.Fixture(block,
            "private static readonly string? Choice = Other; private static readonly string? Other = null;");
        Rejected(root, shape);
    }

    [Fact]
    public void ReadonlyFieldDependencyRetainsIfShape()
    {
        using var root = RelationContractTests.Fixture("Item()", """
            private static readonly bool Choice = Other;
            private static readonly bool Other = true;
            private static DocumentBlock Item()
            {
                if (Choice) return Paragraph(Ref("D5/S0/Test/First"));
                return Paragraph(Ref("D5/S0/Test/Second"));
            }
            """);
        Rejected(root, "IfStatement");
    }

    [Fact]
    public void ConstDiscriminantsRemainReadable()
    {
        using var root = RelationContractTests.Fixture("Paragraph(Ref(Choice ? \"D5/S0/Test/First\" : \"D5/S0/Test/Second\"))",
            "private const bool Choice = Other; private const bool Other = true;");
        RelationContractTests.EqualExecution(root);
    }

    private static void Rejected(TemporaryRoot root, string shape)
    {
        var read = StaticRelationIndexer.Read(root.Path, RelationContractTests.Entry);
        Assert.Null(read.Projection);
        Assert.Equal(shape, read.Failure?.Shape);
    }
}
