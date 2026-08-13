using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static void ValidateFormulas(
        string path,
        string text,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        try
        {
            using var document = JsonDocument.Parse(text.TrimStart('\uFEFF'));
            WalkFormula(document.RootElement, path, findings);
        }
        catch (JsonException exception)
        {
            findings.Add(new RuleFinding(path, $"invalid JSON: {exception.Message}"));
        }
    }

    private static void WalkFormula(
        JsonElement element,
        string path,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            if (element.TryGetProperty("formula", out var formula))
            {
                if (formula.ValueKind == JsonValueKind.Null)
                {
                    // Fixed-shape generated projections use null when a record has no derived formula.
                }
                else if (formula.ValueKind != JsonValueKind.String
                    || !element.TryGetProperty("refs", out var refs)
                    || refs.ValueKind != JsonValueKind.Object)
                {
                    findings.Add(new RuleFinding(path, "formula and refs must be string/object"));
                }
                else
                {
                    try
                    {
                        FormulaValidator.Validate(
                            formula.GetString() ?? string.Empty,
                            refs.EnumerateObject().Select(static item => item.Name).ToHashSet(StringComparer.Ordinal));
                    }
                    catch (FormatException exception)
                    {
                        findings.Add(new RuleFinding(path, exception.Message));
                    }
                }
            }

            foreach (var property in element.EnumerateObject()) WalkFormula(property.Value, path, findings);
        }
        else if (element.ValueKind == JsonValueKind.Array)
        {
            foreach (var child in element.EnumerateArray()) WalkFormula(child, path, findings);
        }
    }
    private sealed class FormulaValidator
    {
        private static readonly Regex TokenPattern = new(
            "\\G\\s*(?:(?<number>[0-9]+(?:\\.[0-9]+)?)|(?<name>[A-Za-z][A-Za-z0-9_.]*)|(?<symbol>.))",
            RegexOptions.CultureInvariant);

        private readonly List<(string Kind, string Value)> tokens;
        private readonly IReadOnlySet<string> references;
        private int index;

        private FormulaValidator(string source, IReadOnlySet<string> references)
        {
            if (!source.All(static character => character <= 0x7f))
            {
                throw new FormatException("formula must be ASCII");
            }

            this.references = references;
            tokens = new List<(string Kind, string Value)>();
            var position = 0;
            while (position < source.Length)
            {
                var match = TokenPattern.Match(source, position);
                if (!match.Success || match.Index != position)
                {
                    throw new FormatException("formula tokenization failed");
                }

                position += match.Length;
                if (match.Groups["number"].Success) tokens.Add(("number", match.Groups["number"].Value));
                else if (match.Groups["name"].Success) tokens.Add(("name", match.Groups["name"].Value));
                else
                {
                    var symbol = match.Groups["symbol"].Value;
                    if (symbol is not ("+" or "-" or "*" or "/" or "(" or ")"))
                    {
                        throw new FormatException($"illegal formula character '{symbol}'");
                    }

                    tokens.Add((symbol, symbol));
                }
            }
        }

        internal static void Validate(string source, IReadOnlySet<string> references)
        {
            var parser = new FormulaValidator(source.Trim(), references);
            parser.Expression();
            if (parser.index != parser.tokens.Count) throw new FormatException("trailing formula tokens");
        }

        private void Expression()
        {
            Term();
            while (Take("+") || Take("-")) Term();
        }

        private void Term()
        {
            Factor();
            while (Take("*") || Take("/")) Factor();
        }

        private void Factor()
        {
            if (Take("+") || Take("-")) { Factor(); return; }
            if (Take("number")) return;
            if (index < tokens.Count && tokens[index].Kind == "name")
            {
                var name = tokens[index++].Value;
                if (name == "sqrt")
                {
                    if (!Take("(")) throw new FormatException("sqrt requires parentheses");
                    Expression();
                    if (!Take(")")) throw new FormatException("sqrt is missing a closing parenthesis");
                }
                else if (!references.Contains(name))
                {
                    throw new FormatException($"unbound formula ref {name}");
                }

                return;
            }

            if (Take("("))
            {
                Expression();
                if (!Take(")")) throw new FormatException("missing closing parenthesis");
                return;
            }

            throw new FormatException("expected formula factor");
        }

        private bool Take(string kind)
        {
            if (index >= tokens.Count || tokens[index].Kind != kind) return false;
            index++;
            return true;
        }
    }
}
