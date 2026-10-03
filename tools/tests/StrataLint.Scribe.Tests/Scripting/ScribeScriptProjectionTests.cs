using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptProjectionTests
{
    [Fact]
    public void EachScriptExecutionLoadsCurrentProjectionFixtures()
    {
        var alpha = Pin("Alpha", 1);
        using var root = new StatementProjectionTestRepository(alpha);
        WriteDefinition(root.Path, "Alpha");
        AssertStatement(ScribeScriptHost.Execute(root.Path, PathFor("Alpha")), "1 = 1");

        root.WriteFixture("pilot", alpha, Pin("Beta", 2));
        WriteDefinition(root.Path, "Beta");

        AssertStatement(ScribeScriptHost.Execute(root.Path, PathFor("Beta")), "2 = 2");
        root.WriteFixture("pilot", Pin("Alpha", 3), Pin("Beta", 4));
        AssertStatement(ScribeScriptHost.Execute(root.Path, PathFor("Alpha")), "3 = 3");
    }

    [Fact]
    public void ScriptBatchSharesFreshProjectionScope()
    {
        using var root = new StatementProjectionTestRepository(Pin("Alpha", 1), Pin("Beta", 1));
        WriteDefinition(root.Path, "Alpha");
        WriteDefinition(root.Path, "Beta");
        root.Run(() => StatementProjectionResolutionTests.AssertProjected(
            LeanDeclarationRef.Create("D5/S0/Test/Alpha.claim"), "1 = 1",
            StatementProjectionResolutionTests.Equality(1)));
        root.WriteFixture("pilot", Pin("Alpha", 2), Pin("Beta", 2));

        var results = StatementProjectionFixtureLoader.WithFreshRepositoryRoot(root.Path, () =>
        {
            StatementProjectionResolutionTests.AssertProjected(
                LeanDeclarationRef.Create("D5/S0/Test/Alpha.claim"), "2 = 2",
                StatementProjectionResolutionTests.Equality(2));
            root.WriteFixture("pilot", Pin("Alpha", 3), Pin("Beta", 3));
            return ScribeScriptHost.ExecuteBatch(root.Path, [PathFor("Alpha"), PathFor("Beta")]);
        });

        Assert.Equal(2, results.Length);
        Assert.All(results, result => AssertStatement(result, "2 = 2"));
        AssertStatement(ScribeScriptHost.Execute(root.Path, PathFor("Alpha")), "3 = 3");
        AssertStatement(ScribeScriptHost.Execute(root.Path, PathFor("Beta")), "3 = 3");
    }

    private static StatementProjectionTestRepository.Pin Pin(string name, int number) =>
        new($"Fixture.{name}.claim", $"D5/S0/Test/{name}.lean",
            StatementProjectionResolutionTests.Equality(number));

    private static void AssertStatement(ScribeScriptResult result, string expected)
    {
        Assert.True(result.IsSuccess, result.Failure?.ToString());
        var section = Assert.IsType<DocumentBlock.Section>(Assert.Single(result.Definition!.Document.Content.Items));
        var statement = Assert.IsType<DocumentBlock.Describe>(Assert.Single(section.Content.Items));
        Assert.IsType<StatementSource.LeanDerived>(statement.StatementSource);
        Assert.Equal(expected, LatexWriter.Write(statement.StatementFormula!));
    }

    private static string PathFor(string name) => $"Blueprint/D5/S0/Test/{name}.scribe.cs";

    private static void WriteDefinition(string root, string name)
    {
        var path = Path.Combine(root, PathFor(name));
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class {{name}} : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("digest", H("title"),
                    Blocks(new DocumentBlock.Section(H("Section"), Blocks(Describe.Lean(DescribeId.Create("claim"),
                        DeclarationHandle.Create("D5/S0/Test/{{name}}.claim"), H("Claim"), StatementSource.FromLean(),
                        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("content"))), DescribeRole.Theorem))))));
            }
            """);
    }
}
