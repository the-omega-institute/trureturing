using System.Text.RegularExpressions;

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
