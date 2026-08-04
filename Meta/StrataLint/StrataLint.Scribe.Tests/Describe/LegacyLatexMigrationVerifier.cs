using System.Collections.Immutable;

namespace StrataLint.Scribe.Tests;

// Migration verifier only. This parser is deliberately confined to Tests and is not an authoring API.
internal static class LegacyLatexMigrationVerifier
{
    internal static Formula ParseStatement(string source)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(source);
        var display = source.StartsWith("$$", StringComparison.Ordinal)
            && source.EndsWith("$$", StringComparison.Ordinal);
        var inline = !display && source.StartsWith('$') && source.EndsWith('$');
        if (!display && !inline)
        {
            throw new FormatException("A legacy statement must have matched $ or $$ delimiters.");
        }

        var body = source[(display ? 2 : 1)..^(display ? 2 : 1)];
        var parser = new Parser(body);
        var content = parser.ParseSequence(inGroup: false);
        if (!parser.AtEnd)
        {
            throw parser.Invalid("unexpected trailing input");
        }

        return new Formula.Layout(
            display ? FormulaLayoutMode.Display : FormulaLayoutMode.Inline,
            content);
    }

    internal static string EmitCSharp(Formula formula) => formula switch
    {
        Formula.Layout value => $"new Formula.Layout(FormulaLayoutMode.{value.Mode}, {EmitCSharp(value.Content)})",
        Formula.LatexSequence value => $"new Formula.LatexSequence([{Join(value.Items)}])",
        Formula.LatexGroup value => $"new Formula.LatexGroup([{Join(value.Items)}])",
        Formula.LatexMacro value => $"new Formula.LatexMacro(FormulaLatexMacro.{value.Value})",
        Formula.LatexSymbol value => $"new Formula.LatexSymbol(FormulaLatexSymbol.{value.Value})",
        Formula.LatexSpace => "new Formula.LatexSpace()",
        Formula.LatexNewline => "new Formula.LatexNewline()",
        Formula.LatexWord value => $"new Formula.LatexWord(FormulaIdentifier.Create(\"{value.Value.Value}\"))",
        Formula.LatexDigits value => $"new Formula.LatexDigits([{string.Join(", ", value.Digits)}])",
        _ => throw new ArgumentException("The migration emitter accepts parsed legacy syntax trees only.", nameof(formula)),
    };

    private static string Join(ImmutableArray<Formula> values) =>
        string.Join(", ", values.Select(EmitCSharp));

    private sealed class Parser(string source)
    {
        private int _offset;
        internal bool AtEnd => _offset == source.Length;

        internal Formula ParseSequence(bool inGroup)
        {
            var items = ImmutableArray.CreateBuilder<Formula>();
            while (!AtEnd && !(inGroup && source[_offset] == '}'))
            {
                items.Add(ParseOne());
            }
            if (inGroup)
            {
                if (AtEnd) throw Invalid("unterminated group");
                _offset++;
            }
            if (items.Count == 0 && !inGroup) throw Invalid("empty statement body");
            return new Formula.LatexSequence(items.ToImmutable());
        }

        private Formula ParseOne()
        {
            var current = source[_offset++];
            if (current == '{')
            {
                var sequence = (Formula.LatexSequence)ParseSequence(inGroup: true);
                return new Formula.LatexGroup(sequence.Items);
            }
            if (current == '}') throw Invalid("unmatched closing brace");
            if (current == ' ') return new Formula.LatexSpace();
            if (current == '\n') return new Formula.LatexNewline();
            if (char.IsAsciiLetter(current))
            {
                var start = _offset - 1;
                while (!AtEnd && char.IsAsciiLetter(source[_offset])) _offset++;
                return new Formula.LatexWord(FormulaIdentifier.Create(source[start.._offset]));
            }
            if (char.IsAsciiDigit(current))
            {
                var digits = ImmutableArray.CreateBuilder<byte>();
                digits.Add((byte)(current - '0'));
                while (!AtEnd && char.IsAsciiDigit(source[_offset])) digits.Add((byte)(source[_offset++] - '0'));
                return new Formula.LatexDigits(digits.ToImmutable());
            }
            if (current == '\\') return ParseMacro();
            return new Formula.LatexSymbol(current switch
            {
                '!' => FormulaLatexSymbol.Exclamation, '&' => FormulaLatexSymbol.Ampersand,
                '\'' => FormulaLatexSymbol.Apostrophe, '(' => FormulaLatexSymbol.OpenParenthesis,
                ')' => FormulaLatexSymbol.CloseParenthesis, '*' => FormulaLatexSymbol.Asterisk,
                '+' => FormulaLatexSymbol.Plus, ',' => FormulaLatexSymbol.Comma,
                '-' => FormulaLatexSymbol.Minus, '.' => FormulaLatexSymbol.Period,
                '/' => FormulaLatexSymbol.Slash, ':' => FormulaLatexSymbol.Colon,
                ';' => FormulaLatexSymbol.Semicolon, '<' => FormulaLatexSymbol.LessThan,
                '=' => FormulaLatexSymbol.Equal, '>' => FormulaLatexSymbol.GreaterThan,
                '[' => FormulaLatexSymbol.OpenBracket, ']' => FormulaLatexSymbol.CloseBracket,
                '^' => FormulaLatexSymbol.Caret, '_' => FormulaLatexSymbol.Underscore,
                '|' => FormulaLatexSymbol.VerticalBar,
                _ => throw Invalid($"unsupported character U+{(int)current:X4}"),
            });
        }

        private Formula ParseMacro()
        {
            if (AtEnd) throw Invalid("trailing backslash");
            var start = _offset;
            if (char.IsAsciiLetter(source[_offset])) while (!AtEnd && char.IsAsciiLetter(source[_offset])) _offset++;
            else _offset++;
            var name = source[start.._offset];
            var enumName = name switch
            {
                "alpha" => "Alpha", "delta" => "DeltaLower", "gamma" => "GammaLower",
                "lambda" => "LambdaLower", "sigma" => "SigmaLower", " " => "EscapedSpace",
                "!" => "NegativeThinSpace", "," => "ThinSpace", ";" => "SemicolonSpace",
                "\\" => "RowBreak", "{" => "OpenBrace", "}" => "CloseBrace",
                _ => char.ToUpperInvariant(name[0]) + name[1..],
            };
            if (!Enum.TryParse<FormulaLatexMacro>(enumName, out var macro))
            {
                throw Invalid($"unsupported macro \\{name}");
            }
            return new Formula.LatexMacro(macro);
        }

        internal FormatException Invalid(string message) =>
            new($"Legacy LaTeX parse error at offset {_offset}: {message}. Source: {source}");
    }
}

public sealed class LegacyLatexMigrationVerifierTests
{
    [Fact]
    public void MigrationVerifierParsesRoundTripsAndEmitsRepresentativeLegacyStatements()
    {
        string[] fixtures =
        {
            "$\\forall n\\in\\mathbb{N},\\ n^{2}\\ge0$",
            "$$\\frac{|\\psi|}{A}=\\frac{12}{A}\\Leftrightarrow|\\psi|=12$$",
            "$$C(q)=\\operatorname{OddTail}\\!\\left(\\operatorname{toList}(q)\\right)$$",
        };

        foreach (var fixture in fixtures)
        {
            var parsed = LegacyLatexMigrationVerifier.ParseStatement(fixture);
            Assert.Equal(fixture, LatexWriter.WriteStatement(parsed));
            Assert.StartsWith(
                "new Formula.Layout(",
                LegacyLatexMigrationVerifier.EmitCSharp(parsed),
                StringComparison.Ordinal);
        }
    }
}
