using System.Text.RegularExpressions;
using static StrataLint.TestSupport.RendererCorpusFixture;

namespace StrataLint.Scribe.Tests;

public sealed partial class FormulaCorpusInventoryTests
{
    /// Macros the emitter can produce, derived rather than listed. Every FormulaLatexMacro
    /// member is rendered and its control words collected, plus the macros LatexWriter emits
    /// from string literals for AST nodes that are not LatexMacro. Both sources are program,
    /// so the alphabet moves when the emitter moves.
    ///
    /// The corpus check below asserts containment, not equality: a Describe node that starts
    /// using an existing capability is legitimate growth and must not turn the suite red,
    /// while a macro outside this set means the emitter cannot produce it. The equality
    /// against a hand-written list this replaces conflated the two -- see #967, where the
    /// list was classified as a corpus observation wired as a reject-outside-set gate with
    /// no source of truth behind it.
    private static IReadOnlyCollection<string> EmitterMacroAlphabet()
    {
        var alphabet = Enum.GetValues<FormulaLatexMacro>()
            .SelectMany(static macro => MacroPattern()
                .Matches(LatexWriter.WriteStatement(new Formula.LatexMacro(macro)))
                .Select(static match => match.Groups[1].Value))
            .ToHashSet(StringComparer.Ordinal);
        foreach (var literal in LiteralEmittedMacros)
        {
            alphabet.Add(literal);
        }

        return alphabet;
    }

    /// Emitted by LatexWriter from string literals rather than through FormulaLatexMacro,
    /// for AST nodes that carry no macro member: Placeholder, Norm, Modulo, NotEqual, and
    /// the non-function branch of FunctionCall/Apply. Named here because they have no
    /// enum to enumerate; each one is a literal in LatexWriter.
    private static readonly string[] LiteralEmittedMacros =
    [
        "bmod", "lVert", "mathit", "mathord", "ne", "rVert",
    ];

    [Fact]
    public void InventoryAllLegacyLatexStatementsAndSyntaxFamilies()
    {
        var definitions = DocumentDefinitions.Discover(DocumentAssembly.Value);
        var entries = definitions
            .SelectMany(static definition => EnumerateDescribe(definition.Document.Content)
                .Where(static node => node.StatementFormula is not null)
                .Select(node => new
                {
                    definition.SourcePath,
                    Value = LatexWriter.WriteStatement(node.StatementFormula!),
                }))
            .ToArray();
        var corpus = string.Join('\n', entries.Select(static entry => entry.Value));
        var macros = MacroPattern().Matches(corpus)
            .Select(static match => match.Groups[1].Value)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.NotEmpty(entries);
        Assert.All(entries, static entry => Assert.NotEmpty(entry.Value));
        var beyondEmitter = macros.Except(EmitterMacroAlphabet(), StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            beyondEmitter.Length == 0,
            $"corpus uses macros the emitter cannot produce: {string.Join(", ", beyondEmitter)}");
        AssertSyntaxFamily(corpus, "quantifier", "\\forall", "\\exists");
        AssertSyntaxFamily(corpus, "logic", "\\land", "\\lor", "\\neg", "\\Rightarrow");
        AssertSyntaxFamily(corpus, "relation", "=", "<", "\\le", "\\ge", "\\in", "\\mid");
        AssertSyntaxFamily(corpus, "norm/absolute", "\\lvert", "\\rvert", "\\Vert", "|");
        AssertSyntaxFamily(corpus, "scripts", "_{", "^{");
        AssertSyntaxFamily(corpus, "sets", "\\subset", "\\subseteq", "\\setminus", "\\mathbb");
        AssertSyntaxFamily(corpus, "fraction", "\\frac");
        AssertSyntaxFamily(corpus, "named function", "\\operatorname");
        AssertSyntaxFamily(corpus, "type arrow", "\\to", "\\mapsto");
        AssertSyntaxFamily(corpus, "large operator", "\\sum", "\\prod", "\\int", "\\lim");
        AssertSyntaxFamily(corpus, "presentation", "\\begin", "\\text", "\\quad");
        AssertRendererVocabularyCoverage(definitions);
    }

    [Fact]
    public void EveryMigratedFormulaHasAStableCorpusAddress()
    {
        var actual = DocumentDefinitions.Discover(DocumentAssembly.Value)
            .OrderBy(static definition => definition.SourcePath, StringComparer.Ordinal)
            .SelectMany(definition => EnumerateDescribe(definition.Document.Content)
                .Where(static node => node.StatementFormula is not null)
                .Select((node, ordinal) => new
                {
                    SourcePath = CanonicalBlueprintPath(definition.SourcePath),
                    DescribeId = node.Id.Value,
                    Ordinal = ordinal,
                    Canonical = LatexWriter.WriteStatement(node.StatementFormula!),
                }))
            .ToArray();

        Assert.NotEmpty(actual);
        Assert.Equal(actual.Length, actual.Select(static entry =>
            (entry.SourcePath, entry.DescribeId, entry.Ordinal)).Distinct().Count());
        Assert.All(actual, static entry => Assert.NotEmpty(entry.Canonical));
    }

    private static void AssertSyntaxFamily(string corpus, string family, params string[] tokens) =>
        Assert.True(tokens.Any(corpus.Contains), $"Formula corpus is missing the {family} family.");

    private static IEnumerable<DocumentBlock.Describe> EnumerateDescribe(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            if (block is DocumentBlock.Describe describe)
            {
                yield return describe;
                foreach (var nested in EnumerateDescribe(describe.Content))
                {
                    yield return nested;
                }
            }
            else if (block is DocumentBlock.Section section)
            {
                foreach (var nested in EnumerateDescribe(section.Content))
                {
                    yield return nested;
                }
            }
        }
    }

    private static string CanonicalBlueprintPath(string sourcePath)
    {
        const string prefix = "Blueprint/";
        var normalized = sourcePath.Replace('\\', '/');
        var index = normalized.IndexOf(prefix, StringComparison.Ordinal);
        return index >= 0
            ? normalized[index..]
            : throw new ArgumentException("Scribe source path is outside Blueprint.", nameof(sourcePath));
    }


    [GeneratedRegex(@"(?<!\\)\\([A-Za-z]+)", RegexOptions.CultureInvariant)]
    private static partial Regex MacroPattern();
}
