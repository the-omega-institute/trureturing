using System.Text.RegularExpressions;

namespace StrataLint.Scribe.Tests;

public sealed partial class FormulaCorpusInventoryTests
{
    [Fact]
    public void BlueprintAuthorSurfaceContainsNoLinearFormulaTokenTrees()
    {
        var blueprint = Path.Combine(FindRepositoryRoot(), "Blueprint");
        var forbidden = new[] { "FormulaTokens", "Formula.TokenTree", "FormulaToken", "FormulaMark", "FormulaSpace" };

        var residuals = Directory.EnumerateFiles(blueprint, "*.scribe.cs", SearchOption.AllDirectories)
            .SelectMany(path => forbidden
                .Where(name => File.ReadAllText(path).Contains(name, StringComparison.Ordinal))
                .Select(name => $"{Path.GetRelativePath(blueprint, path)}:{name}"))
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(residuals);
    }

    private static readonly string[] ExpectedMacros =
    [
        "Delta", "Gamma", "Lambda", "Leftrightarrow", "Re", "Rightarrow",
        "Vert", "alpha", "begin", "beta", "cdot", "circ", "delta", "ell",
        "emptyset", "end", "equiv", "exists", "forall", "frac", "gamma",
        "gcd", "ge", "geq", "iff", "implies", "in", "infty", "int", "iota",
        "kappa", "lVert", "lambda", "land", "langle", "le", "left", "leq",
        "lfloor", "lim", "log", "lor", "lvert", "mapsto",
        "mathbb", "mathbf", "mathcal", "mathit", "mathord", "mathrm", "max", "mid", "min",
        "mu", "ne", "neg", "neq", "nu", "omega", "operatorname", "overline", "perp",
        "phi", "pi", "pm", "prod", "psi", "qquad", "quad", "rVert", "rangle", "rfloor",
        "rho", "right", "rvert", "setminus", "sigma", "sim", "sin", "sqrt",
        "subset", "subseteq", "sum", "tau", "text", "theta", "times", "to",
        "varepsilon", "varnothing", "varphi", "widehat", "widetilde", "xi", "zeta",
    ];

    [Fact]
    public void InventoryAllLegacyLatexStatementsAndSyntaxFamilies()
    {
        var entries = DocumentDefinitions.All
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

        Assert.Equal(166, entries.Length);
        Assert.Equal(77, entries.Select(static entry => entry.SourcePath).Distinct().Count());
        Assert.Equal(ExpectedMacros, macros);
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
    }

    [Fact]
    public void EveryMigratedFormulaHasAStableCorpusAddress()
    {
        var actual = DocumentDefinitions.All
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

        Assert.Equal(166, actual.Length);
        Assert.Equal(166, actual.Select(static entry =>
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

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "CLAUDE.md")))
        {
            directory = directory.Parent;
        }

        return directory?.FullName
            ?? throw new DirectoryNotFoundException("Repository root was not found.");
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
