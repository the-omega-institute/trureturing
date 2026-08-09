using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class ScribeProseAssertionRule
{
    private const string ScribeTestsPrefix =
        "Meta/StrataLint/StrataLint.Scribe.Tests/";

    private static readonly Regex LocalDeclarationPattern = new(
        """(?ms)^[\t ]*(?:var|string)[\t ]+(?<name>[A-Za-z_][A-Za-z0-9_]*)[\t ]*=[\t ]*(?<initializer>.*?);[\t ]*(?://[^\r\n]*)?\r?$""",
        RegexOptions.CultureInvariant);

    private static readonly Regex ParagraphTextInitializerPattern = new(
        """(?s)Assert\s*\.\s*IsType\s*<\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*\.\s*)*Inline\s*\.\s*Text\s*>.*?\.\s*Content\s*\.\s*Items.*?\.\s*Run\s*\.\s*Value""",
        RegexOptions.CultureInvariant);

    private static readonly Regex RenderedMarkdownInitializerPattern = new(
        """(?s)Encoding\s*\.\s*UTF8\s*\.\s*GetString\s*\(.*?CanonicalMarkdownWriter\s*\.\s*Write\s*\(""",
        RegexOptions.CultureInvariant);

    private static readonly Regex LiteralAssertionPattern = new(
        """Assert\s*\.\s*(?<assertion>Contains|DoesNotContain)\s*\(\s*@?"(?:""|\\.|[^"\r\n])*"\s*,\s*(?<subject>[A-Za-z_][A-Za-z0-9_]*)\s*(?:,|\))""",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        context.Current.Files.Values
            .Where(static file => IsScribeTestSource(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .SelectMany(static file => Inspect(file.Path.Value, file.Text))
            .ToImmutableArray();

    private static IEnumerable<RuleFinding> Inspect(string path, string source)
    {
        var renderedProseDeclarations = LocalDeclarationPattern.Matches(source)
            .Where(match => IsRenderedProseInitializer(
                path,
                match.Groups["initializer"].Value))
            .Select(static match => new
            {
                Name = match.Groups["name"].Value,
                End = match.Index + match.Length,
            })
            .ToArray();

        foreach (Match match in LiteralAssertionPattern.Matches(source))
        {
            var subject = match.Groups["subject"].Value;
            if (!renderedProseDeclarations.Any(declaration =>
                    string.Equals(declaration.Name, subject, StringComparison.Ordinal)
                    && declaration.End <= match.Index
                    && source.IndexOf(
                        '}',
                        declaration.End,
                        match.Index - declaration.End) < 0))
            {
                continue;
            }

            yield return new RuleFinding(
                path,
                $"literal Assert.{match.Groups["assertion"].Value} against rendered document prose duplicates the Scribe source; assert structure or deterministic re-emission instead");
        }
    }

    private static bool IsRenderedProseInitializer(string path, string initializer) =>
        ParagraphTextInitializerPattern.IsMatch(initializer)
        || (path.Contains("/Describe/", StringComparison.Ordinal)
            && path.EndsWith("DocumentTests.cs", StringComparison.Ordinal)
            && RenderedMarkdownInitializerPattern.IsMatch(initializer));

    private static bool IsScribeTestSource(string path) =>
        path.StartsWith(ScribeTestsPrefix, StringComparison.Ordinal)
        && path.EndsWith(".cs", StringComparison.Ordinal);
}
