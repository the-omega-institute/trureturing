using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeProseAssertionRuleTests
{
    private const string ScribeTestsPath =
        "Meta/StrataLint/StrataLint.Scribe.Tests";
    private const string TestPath =
        "Meta/StrataLint/StrataLint.Scribe.Tests/Describe/SyntheticDocumentTests.cs";

    [Fact]
    public void JoinedParagraphProseLiteralAssertionIsBlocked()
    {
        const string source = """
            var prose = string.Join(
                " ",
                describe.Content.Items
                    .OfType<DocumentBlock.Paragraph>()
                    .Select(static paragraph =>
                        Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
            Assert.Contains("copied document sentence", prose, StringComparison.Ordinal);
            """;

        var diagnostic = Assert.Single(Evaluate(source));

        Assert.Equal("SL-024", diagnostic.RuleId.Value);
        Assert.Equal(DisplaySeverity.Error, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(TestPath, diagnostic.Path);
        Assert.Equal(
            "literal Assert.Contains against rendered document prose duplicates the Scribe source; assert structure or deterministic re-emission instead",
            diagnostic.Message);
    }

    [Fact]
    public void DirectParagraphTextAndRenderedMarkdownAreBlocked()
    {
        const string source = """
            var prose = Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value;
            Assert.DoesNotContain("copied paragraph sentence", prose, StringComparison.Ordinal);

            var markdown = Encoding.UTF8.GetString(
                CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
            Assert.Contains("copied markdown sentence", markdown, StringComparison.Ordinal);
            """;

        var diagnostics = Evaluate(source);

        Assert.Equal(2, diagnostics.Length);
        Assert.Contains(diagnostics, static diagnostic =>
            diagnostic.Message.StartsWith("literal Assert.DoesNotContain", StringComparison.Ordinal));
        Assert.Contains(diagnostics, static diagnostic =>
            diagnostic.Message.StartsWith("literal Assert.Contains", StringComparison.Ordinal));
    }

    [Fact]
    public void AliasPropagationIsOutsideTheTextShapedPredicate()
    {
        const string source = """
            var prose = Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value;
            var rendered = prose;
            Assert.Contains("copied paragraph sentence", rendered, StringComparison.Ordinal);
            """;

        Assert.Empty(Evaluate(source));
    }

    [Fact]
    public void StructuralLiteralAssertionsRemainLegal()
    {
        const string source = """
            var latex = LatexWriter.WriteStatement(describe.StatementFormula!);
            Assert.Contains(@"\sum_{i}p(i)=1", latex, StringComparison.Ordinal);

            var declarationNames = describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
            Assert.Contains("D5/S3/Fixture.theorem_name", declarationNames);
            Assert.DoesNotContain(
                describes,
                static describe => describe.Kind == DescribeKind.Remark);
            """;

        Assert.Empty(Evaluate(source));
    }

    [Fact]
    public void RenderedProseLocalDoesNotTaintSameNamedStructuralLocalInAnotherMethod()
    {
        const string source = """
            public sealed class SyntheticDocumentTests
            {
                public void RenderedProse()
                {
                    var value = Assert.IsType<Inline.Text>(
                        Assert.Single(paragraph.Content.Items)).Run.Value;
                }

                public void StructuralLatex()
                {
                    var value = LatexWriter.WriteStatement(describe.StatementFormula!);
                    Assert.Contains(@"\sum_{i}p(i)=1", value, StringComparison.Ordinal);
                }
            }
            """;

        Assert.Empty(EvaluateFile(source));
    }

    [Fact]
    public void RepositoryScribeTestsHaveNoCopiedProseAssertions()
    {
        var root = FindRepositoryRoot();
        var fixture = new RuleFixture();
        foreach (var path in Directory.EnumerateFiles(
                     Path.Combine(root, ScribeTestsPath),
                     "*.cs",
                     SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/');
            fixture.Files[relative] = File.ReadAllText(path);
        }

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(24),
            fixture.Build()).Diagnostics;

        Assert.True(
            diagnostics.IsEmpty,
            string.Join("\n", diagnostics.Select(static diagnostic => diagnostic.Render())));
    }

    private static System.Collections.Immutable.ImmutableArray<Diagnostic> Evaluate(string source)
    {
        return EvaluateFile($$"""
            public sealed class SyntheticDocumentTests
            {
                public void Test()
                {
                    {{source}}
                }
            }
            """);
    }

    private static System.Collections.Immutable.ImmutableArray<Diagnostic> EvaluateFile(string source)
    {
        var fixture = new RuleFixture();
        fixture.Files[TestPath] = source;

        return RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(24),
            fixture.Build()).Diagnostics;
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (Directory.Exists(Path.Combine(current.FullName, ScribeTestsPath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
