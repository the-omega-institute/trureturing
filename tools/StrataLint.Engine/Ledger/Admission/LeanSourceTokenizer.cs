using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record LeanSourceToken(
    string Text, int Line, int Column, ImmutableArray<string> IdentifierParts = default, int ByteOffset = 0)
{
    internal bool IsIdentifier => !IdentifierParts.IsDefaultOrEmpty;
    internal string Identifier => LeanSourceTokenizer.IdentifierText(IdentifierParts);
}

internal static class LeanSourceTokenizer
{
    // The registered alternative can expose a source dependency only when the
    // suffix starts an identifier. Delimiter and escaped Char literals remain
    // literal controls during the demand probe; production scanning is unchanged.
    internal static bool EqualityCanExposeIdentifier(string source, int byteOffset)
    {
        var utf8 = Encoding.UTF8.GetBytes(source);
        var index = Encoding.UTF8.GetCharCount(utf8.AsSpan(0, byteOffset)) + 2;
        return index < source.Length && IsIdentifierStart(char.ConvertToUtf32(source, index));
    }
    internal static ImmutableArray<LeanSourceToken> Tokenize(string source, Func<int, bool>? equalityAt = null) =>
        new Scanner(source, includeInterpolationTerms: false, equalityAt, null).ReadCode();

    // Proposition extraction retains literal spelling; source policies also inspect embedded terms.
    internal static ImmutableArray<LeanSourceToken> TokenizeIncludingInterpolationTerms(string source, Func<int, bool>? equalityAt = null, Action<LeanSourceToken>? observe = null) =>
        new Scanner(source, includeInterpolationTerms: true, equalityAt, observe).ReadCode();

    internal static ImmutableArray<string> IdentifierParts(string text)
    {
        var tokens = Tokenize(text);
        return tokens.Length == 1 && tokens[0].IsIdentifier ? tokens[0].IdentifierParts : [];
    }

    internal static string IdentifierText(IEnumerable<string> parts) =>
        string.Join('.', parts.Select(static part =>
            part.Length > 0 && part[0] != '\u00ab' && IsIdentifierStart(char.ConvertToUtf32(part, 0))
                && part.EnumerateRunes().Skip(1).All(static rune => IsIdentifierPart(rune.Value))
                    ? part
                    : "\u00ab" + part + "\u00bb"));

    private sealed class Scanner(string source, bool includeInterpolationTerms, Func<int, bool>? equalityAt, Action<LeanSourceToken>? observe)
    {
        private int index;
        private int line = 1;
        private int column;

        internal ImmutableArray<LeanSourceToken> ReadCode(int? interpolationLine = null)
        {
            var result = ImmutableArray.CreateBuilder<LeanSourceToken>();
            var brackets = new Stack<(char Symbol, int Line)>();
            while (index < source.Length)
            {
                if (char.IsWhiteSpace(source[index]))
                {
                    Advance();
                    continue;
                }

                if (At("--"))
                {
                    while (index < source.Length && source[index] != '\n')
                    {
                        Advance();
                    }

                    continue;
                }

                if (At("/-"))
                {
                    ReadComment();
                    continue;
                }

                if (interpolationLine is not null && source[index] == '}' && brackets.Count == 0)
                {
                    Advance();
                    return result.ToImmutable();
                }

                var start = index;
                var tokenLine = line;
                var tokenColumn = column;
                var identifierParts = ImmutableArray<string>.Empty;
                var rawQuote = RawStringQuote();
                if (rawQuote >= 0)
                {
                    ReadRawString(rawQuote);
                }
                else if (source[index] == '"')
                {
                    var interpolated = result.Count > 0 && result[^1].Text is "s!" or "m!" or "f!";
                    ReadString(interpolated, result);
                }
                // Lean tokenFnAux excludes doubled apostrophes from character-literal dispatch.
                else if (source[index] == '\'' && !At("''"))
                {
                    ReadCharacter();
                }
                else if (NameLiteralPrefixLength() is var prefix && prefix > 0)
                {
                    Advance(prefix);
                    ReadIdentifier();
                }
                else if (IsIdentifierStart(CodePointAt(index)))
                {
                    identifierParts = ReadIdentifier();
                }
                else
                {
                    var symbol = source.Substring(index, SymbolLength());
                    Advance(symbol.Length);
                    // Keep the structural delimiter separate for proposition consumers.
                    if (symbol == "]'")
                    {
                        result.Add(new LeanSourceToken("]", tokenLine, tokenColumn, ByteOffset: Encoding.UTF8.GetByteCount(source.AsSpan(0, start))));
                        symbol = "]";
                        start++;
                        tokenColumn++;
                    }

                    if (symbol.Length == 1 && symbol[0] is '(' or '[' or '{')
                    {
                        brackets.Push((symbol[0], tokenLine));
                    }
                    else if (symbol.Length == 1 && symbol[0] is ')' or ']' or '}')
                    {
                        var expected = symbol[0] switch { ')' => '(', ']' => '[', _ => '{' };
                        if (!brackets.TryPop(out var actual) || actual.Symbol != expected)
                        {
                            throw Error("Lean delimiters are unbalanced.", tokenLine);
                        }
                    }
                }

                var token = new LeanSourceToken(source[start..index], tokenLine, tokenColumn, identifierParts, Encoding.UTF8.GetByteCount(source.AsSpan(0, start)));
                result.Add(token);
                observe?.Invoke(token);
            }

            if (brackets.TryPeek(out var opening))
            {
                throw Error("Lean delimiters are unbalanced.", opening.Line);
            }

            if (interpolationLine is not null)
            {
                throw Error("Lean string interpolation is unterminated.", interpolationLine.Value);
            }

            return result.ToImmutable();
        }

        private int SymbolLength()
        {
            // Lean 4.33 tokenFnAux uses the longest registered prefix. This bounded
            // symbolic-prime class comes from getTokenTable after importing mathlib
            // db584cd6 and opening its relevant scopes, plus local notation inspection.
            // Identifier-like spellings retain ReadIdentifier's existing projection.
            if (At("\u207b\u00b9'o"))
            {
                return 4;
            }

            if (At("\u207b\u00b9'") || At("\u03a3\u2097'") || At("''\u1d41"))
            {
                return 3;
            }

            // Only the bracketed order tokens are registered; their bare stems are not.
            // Leave '[' for delimiter tracking, as with the existing sum/product tokens.
            if (At("\u227a'[") || At("\u227c'["))
            {
                return 2;
            }

            // Current Lean supplies availability at this byte site. The spelling
            // projection still owns longest-token selection and literal handling.
            if (At("='") && (equalityAt?.Invoke(Encoding.UTF8.GetByteCount(source.AsSpan(0, index))) ?? false))
            {
                return 2;
            }

            return index + 1 < source.Length && source.Substring(index, 2) is
                ":=" or "=>" or "->" or "<-" or "::" or "<=" or ">=" or "==" or "!="
                    or "''" or "]'" or "#'" or "\u00d7'" or "\u03a3'" or "\u2200'" or "\u2203'"
                    or "\u220f'" or "\u2211'" or "\u2218'" or "\u2295'" or "\u2297'" or "\u27e7'"
                        ? 2
                        : char.IsSurrogatePair(source, index) ? 2 : 1;
        }

        private void ReadComment()
        {
            var startLine = line;
            var depth = 0;
            do
            {
                if (At("/-"))
                {
                    depth++;
                    Advance(2);
                }
                else if (At("-/"))
                {
                    depth--;
                    Advance(2);
                }
                else
                {
                    Advance();
                }
            }
            while (index < source.Length && depth > 0);
            if (depth != 0)
            {
                throw Error("Lean block comment is unterminated.", startLine);
            }
        }

        private void ReadString(bool interpolated, ImmutableArray<LeanSourceToken>.Builder result)
        {
            var startLine = line;
            Advance();
            while (index < source.Length)
            {
                var value = source[index];
                if (value == '\\')
                {
                    Advance();
                    if (index < source.Length)
                    {
                        Advance();
                    }
                }
                else if (value == '"')
                {
                    Advance();
                    return;
                }
                else if (interpolated && value == '{')
                {
                    var interpolationLine = line;
                    Advance();
                    var terms = ReadCode(interpolationLine);
                    if (includeInterpolationTerms)
                    {
                        result.AddRange(terms);
                    }
                }
                else
                {
                    Advance();
                }
            }

            throw Error("Lean string literal is unterminated.", startLine);
        }

        private int RawStringQuote()
        {
            if (source[index] != 'r')
            {
                return -1;
            }

            var cursor = index + 1;
            while (cursor < source.Length && source[cursor] == '#')
            {
                cursor++;
            }

            return cursor < source.Length && source[cursor] == '"' ? cursor : -1;
        }

        private void ReadRawString(int quote)
        {
            var startLine = line;
            var terminator = "\"" + new string('#', quote - index - 1);
            Advance(quote - index + 1);
            while (index < source.Length)
            {
                if (At(terminator))
                {
                    Advance(terminator.Length);
                    return;
                }

                Advance();
            }

            throw Error("Lean raw string literal is unterminated.", startLine);
        }

        private void ReadCharacter()
        {
            var length = CharacterLiteralLength(index, out var error);
            if (error is not null)
            {
                throw Error(error, line);
            }

            Advance(length);
        }

        private int CharacterLiteralLength(int start, out string? error)
        {
            var cursor = start + 1;
            if (cursor < source.Length && source[cursor] == '\\')
            {
                cursor++;
                if (cursor < source.Length)
                {
                    var escape = source[cursor++];
                    // Lean 4.33 quotedCharFn uses this finite simple-escape alphabet.
                    if (escape is not ('\\' or '"' or '\'' or 'r' or 'n' or 't' or 'x' or 'u'))
                    {
                        error = "Lean character escape is malformed.";
                        return 0;
                    }

                    var digits = escape switch { 'x' => 2, 'u' => 4, _ => 0 };
                    for (var count = 0; count < digits; count++)
                    {
                        if (cursor >= source.Length || !char.IsAsciiHexDigit(source[cursor]))
                        {
                            error = "Lean character escape is malformed.";
                            return 0;
                        }

                        cursor++;
                    }
                }
            }
            else if (cursor < source.Length)
            {
                cursor += char.IsSurrogatePair(source, cursor) ? 2 : 1;
            }

            if (cursor >= source.Length || source[cursor] != '\'')
            {
                error = "Lean character literal is unterminated or malformed.";
                return 0;
            }

            error = null;
            return cursor - start + 1;
        }

        private int NameLiteralPrefixLength()
        {
            var length = At("``") ? 2 : At("`") ? 1 : 0;
            return length > 0 && index + length < source.Length && IsIdentifierStart(CodePointAt(index + length))
                ? length
                : 0;
        }

        private ImmutableArray<string> ReadIdentifier()
        {
            var parts = ImmutableArray.CreateBuilder<string>();
            while (index < source.Length)
            {
                if (source[index] == '\u00ab')
                {
                    var startLine = line;
                    Advance();
                    var start = index;
                    while (index < source.Length && source[index] != '\u00bb')
                    {
                        Advance();
                    }

                    if (index == source.Length)
                    {
                        throw Error("Lean escaped identifier is unterminated.", startLine);
                    }

                    parts.Add(source[start..index]);
                    Advance();
                }
                else
                {
                    var start = index;
                    while (index < source.Length && IsIdentifierPart(CodePointAt(index)))
                    {
                        Advance(char.IsSurrogatePair(source, index) ? 2 : 1);
                    }

                    parts.Add(source[start..index]);
                }

                if (index + 1 >= source.Length || source[index] != '.' || !IsIdentifierStart(CodePointAt(index + 1)))
                {
                    return parts.ToImmutable();
                }

                Advance();
            }

            return parts.ToImmutable();
        }

        private bool At(string text) => source.AsSpan(index).StartsWith(text, StringComparison.Ordinal);

        private int CodePointAt(int offset) => char.ConvertToUtf32(source, offset);

        private static LeanSourceExtractionException Error(string message, int atLine) => new(message, atLine, lexical: true);

        private void Advance(int count = 1)
        {
            for (var offset = 0; offset < count; offset++)
            {
                if (source[index++] == '\n')
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
    }

    // Lean v4.33.0 Init/Meta/Defs.lean defines explicit isIdFirst/isIdRest ranges.
    private static bool IsIdentifierStart(int value) =>
        value is '_' or '\u00ab' or >= 'a' and <= 'z' or >= 'A' and <= 'Z'
        || IsLetterLike(value);

    private static bool IsIdentifierPart(int value) =>
        value != '\u00ab' && IsIdentifierStart(value)
        || value is '\'' or '!' or '?' or >= '0' and <= '9'
            or >= 0x2080 and <= 0x2089
            or >= 0x2090 and <= 0x209c
            or >= 0x1d62 and <= 0x1d6a
            or 0x2c7c;

    private static bool IsLetterLike(int value) => value is
        >= 0x03b1 and <= 0x03c9 and not 0x03bb
        or >= 0x0391 and <= 0x03a9 and not 0x03a0 and not 0x03a3
        or >= 0x03ca and <= 0x03fb
        or >= 0x1f00 and <= 0x1ffe
        or >= 0x2100 and <= 0x214f
        or >= 0x1d49c and <= 0x1d59f
        or >= 0x00c0 and <= 0x00ff and not 0x00d7 and not 0x00f7
        or >= 0x0100 and <= 0x017f;
}
