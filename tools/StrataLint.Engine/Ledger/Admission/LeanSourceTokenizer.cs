using System.Collections.Immutable;
using System.Globalization;

namespace StrataLint.Engine;

internal sealed record LeanSourceToken(string Text, int Line, int Column);

internal static class LeanSourceTokenizer
{
    internal static ImmutableArray<LeanSourceToken> Tokenize(string source)
    {
        var result = ImmutableArray.CreateBuilder<LeanSourceToken>();
        var brackets = new Stack<char>();
        var index = 0;
        var line = 1;
        var column = 0;
        while (index < source.Length)
        {
            if (char.IsWhiteSpace(source[index]))
            {
                Advance(source[index]);
                index++;
                continue;
            }

            if (index + 1 < source.Length && source[index] == '-' && source[index + 1] == '-')
            {
                while (index < source.Length && source[index] != '\n')
                {
                    Advance(source[index++]);
                }

                continue;
            }

            if (index + 1 < source.Length && source[index] == '/' && source[index + 1] == '-')
            {
                var depth = 0;
                do
                {
                    if (index + 1 < source.Length && source[index] == '/' && source[index + 1] == '-')
                    {
                        depth++;
                        Advance(source[index++]);
                        Advance(source[index++]);
                    }
                    else if (index + 1 < source.Length && source[index] == '-' && source[index + 1] == '/')
                    {
                        depth--;
                        Advance(source[index++]);
                        Advance(source[index++]);
                    }
                    else
                    {
                        Advance(source[index++]);
                    }
                }
                while (index < source.Length && depth > 0);
                if (depth != 0)
                {
                    throw new LeanSourceExtractionException("Lean block comment is unterminated.");
                }

                continue;
            }

            var tokenLine = line;
            var tokenColumn = column;
            if (source[index] == '"')
            {
                var start = index;
                Advance(source[index++]);
                var closed = false;
                while (index < source.Length)
                {
                    if (source[index] == '\\' && index + 1 < source.Length)
                    {
                        Advance(source[index++]);
                        Advance(source[index++]);
                        continue;
                    }

                    var value = source[index];
                    Advance(source[index++]);
                    if (value == '"')
                    {
                        closed = true;
                        break;
                    }
                }

                if (!closed)
                {
                    throw new LeanSourceExtractionException("Lean string literal is unterminated.");
                }

                result.Add(new LeanSourceToken(source[start..index], tokenLine, tokenColumn));
                continue;
            }

            if (IsIdentifierStart(source[index]))
            {
                var start = index;
                while (index < source.Length && IsIdentifierPart(source[index]))
                {
                    Advance(source[index++]);
                }

                result.Add(new LeanSourceToken(source[start..index], tokenLine, tokenColumn));
                continue;
            }

            var symbol = index + 1 < source.Length && source.Substring(index, 2) is
                ":=" or "=>" or "->" or "<-" or "::" or "<=" or ">=" or "==" or "!="
                    ? source.Substring(index, 2)
                    : source[index].ToString(CultureInfo.InvariantCulture);
            foreach (var value in symbol)
            {
                Advance(value);
            }

            index += symbol.Length;
            if (symbol.Length == 1 && symbol[0] is '(' or '[' or '{')
            {
                brackets.Push(symbol[0]);
            }
            else if (symbol.Length == 1 && symbol[0] is ')' or ']' or '}')
            {
                var expected = symbol[0] switch { ')' => '(', ']' => '[', _ => '{' };
                if (!brackets.TryPop(out var actual) || actual != expected)
                {
                    throw new LeanSourceExtractionException("Lean delimiters are unbalanced.");
                }
            }

            result.Add(new LeanSourceToken(symbol, tokenLine, tokenColumn));
        }

        if (brackets.Count != 0)
        {
            throw new LeanSourceExtractionException("Lean delimiters are unbalanced.");
        }

        return result.ToImmutable();

        void Advance(char value)
        {
            if (value == '\n')
            {
                line++;
                column = 0;
            }
            else
            {
                column++;
            }
        }
    }

    private static bool IsIdentifierStart(char value) =>
        value == '_'
        || char.IsLetter(value)
        || char.GetUnicodeCategory(value) is UnicodeCategory.LetterNumber;

    private static bool IsIdentifierPart(char value) =>
        IsIdentifierStart(value)
        || char.IsDigit(value)
        || value is '\'' or '.'
        || char.GetUnicodeCategory(value) is
            UnicodeCategory.NonSpacingMark
            or UnicodeCategory.SpacingCombiningMark
            or UnicodeCategory.OtherNumber;
}
