using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class TaskBlockReferenceSyntax
{
    // RepositoryRules consumes this exact dev token grammar; MISSION tightens it below.
    private const string TaskTokenExpression = "TASK\\s+(?<code>D5-T[0-9]{4})";

    internal static readonly Regex TaskTokenPattern = new(
        TaskTokenExpression,
        RegexOptions.CultureInvariant);

    private const string MissionTaskTokenExpression =
        TaskTokenExpression + "(?![A-Za-z0-9_])";

    private static readonly Regex DocumentationCommentTaskPattern = new(
        "^[\\t ]*(?<open>/--)[\\t ]+" + MissionTaskTokenExpression,
        RegexOptions.CultureInvariant | RegexOptions.Multiline);

    internal static int CountDocumentationCommentTaskStarts(string text, string caseId)
    {
        ArgumentNullException.ThrowIfNull(text);
        ArgumentException.ThrowIfNullOrWhiteSpace(caseId);

        var activeStarts = CollectTopLevelDocumentationCommentStarts(text);
        return DocumentationCommentTaskPattern.Matches(text)
            .Count(match => activeStarts.Contains(match.Groups["open"].Index)
                && string.Equals(
                    match.Groups["code"].Value,
                    caseId,
                    StringComparison.Ordinal));
    }

    private static HashSet<int> CollectTopLevelDocumentationCommentStarts(string text)
    {
        var starts = new HashSet<int>();

        // This is lexical-state tracking only: it decides whether a /-- opener is active,
        // not whether the surrounding Lean parses. The pinned v4.31.0 states that can make
        // /-, -/, --, or " bytes inert are comments, quoted strings/chars, raw strings,
        // guillemet identifiers, and interpolated-string literal chunks. Numerals, ordinary
        // identifiers, and other tokens do not change those bytes and are intentionally out of scope.
        for (var index = 0; index < text.Length;)
        {
            var current = text[index];
            var next = index + 1 < text.Length ? text[index + 1] : '\0';

            if (current == '-' && next == '-')
            {
                index = SkipLineComment(text, index + 2);
                continue;
            }

            if (current == '/' && next == '-')
            {
                if (index + 2 < text.Length && text[index + 2] == '-')
                {
                    starts.Add(index);
                }

                index = SkipBlockComment(text, index + 2);
                continue;
            }

            if (TrySkipRawString(text, index, out var rawStringEnd))
            {
                index = rawStringEnd;
                continue;
            }

            if (current == '\'' && IsCharacterLiteralStart(text, index))
            {
                index = SkipCharacterLiteral(text, index + 1);
                continue;
            }

            if (current == '«')
            {
                index = SkipGuillemetIdentifier(text, index + 1);
                continue;
            }

            if (current == '"')
            {
                index = IsInterpolatedStringStart(text, index)
                    ? SkipInterpolatedString(text, index + 1)
                    : SkipQuoted(text, index + 1, '"');
                continue;
            }

            index++;
        }

        return starts;
    }

    private static int SkipLineComment(string text, int index)
    {
        while (index < text.Length && text[index] != '\n')
        {
            index++;
        }

        return index < text.Length ? index + 1 : index;
    }

    private static int SkipBlockComment(string text, int index)
    {
        var depth = 1;
        while (index < text.Length && depth > 0)
        {
            if (index + 1 < text.Length && text[index] == '/' && text[index + 1] == '-')
            {
                depth++;
                index += 2;
            }
            else if (index + 1 < text.Length && text[index] == '-' && text[index + 1] == '/')
            {
                depth--;
                index += 2;
            }
            else
            {
                index++;
            }
        }

        return index;
    }

    private static int SkipQuoted(string text, int index, char quote)
    {
        while (index < text.Length)
        {
            if (text[index] == '\\' && index + 1 < text.Length)
            {
                index += 2;
            }
            else if (text[index] == quote)
            {
                return index + 1;
            }
            else
            {
                index++;
            }
        }

        return index;
    }

    private static bool TrySkipRawString(string text, int index, out int end)
    {
        end = index;
        if (text[index] != 'r' || !IsTokenStart(text, index))
        {
            return false;
        }

        var delimiter = index + 1;
        while (delimiter < text.Length && text[delimiter] == '#')
        {
            delimiter++;
        }

        if (delimiter >= text.Length || text[delimiter] != '"')
        {
            return false;
        }

        var hashCount = delimiter - index - 1;
        var cursor = delimiter + 1;
        while (cursor < text.Length)
        {
            if (text[cursor] == '"' && HasClosingHashes(text, cursor + 1, hashCount))
            {
                end = cursor + hashCount + 1;
                return true;
            }

            cursor++;
        }

        end = text.Length;
        return true;
    }

    private static bool HasClosingHashes(string text, int index, int hashCount)
    {
        if (index + hashCount > text.Length)
        {
            return false;
        }

        for (var offset = 0; offset < hashCount; offset++)
        {
            if (text[index + offset] != '#')
            {
                return false;
            }
        }

        return true;
    }

    private static bool IsCharacterLiteralStart(string text, int index)
    {
        return index + 1 < text.Length
            && text[index + 1] != '\''
            && IsTokenStart(text, index);
    }

    private static int SkipCharacterLiteral(string text, int index)
    {
        if (index >= text.Length)
        {
            return index;
        }

        if (text[index] == '\\')
        {
            index++;
            if (index >= text.Length)
            {
                return index;
            }

            index += text[index] switch
            {
                'x' => Math.Min(3, text.Length - index),
                'u' => Math.Min(5, text.Length - index),
                _ => 1,
            };
        }
        else if (char.IsHighSurrogate(text[index])
                 && index + 1 < text.Length
                 && char.IsLowSurrogate(text[index + 1]))
        {
            index += 2;
        }
        else
        {
            index++;
        }

        return index < text.Length && text[index] == '\'' ? index + 1 : index;
    }

    private static bool IsTokenStart(string text, int index)
    {
        return index == 0 || !IsIdentifierContinuation(text[index - 1]);
    }

    private static bool IsIdentifierContinuation(char value)
    {
        return char.IsLetterOrDigit(value)
            || value is '_' or '\'' or '!' or '?' or '»'
            || value >= 0x80;
    }

    private static int SkipGuillemetIdentifier(string text, int index)
    {
        while (index < text.Length && text[index] != '»')
        {
            index++;
        }

        return index < text.Length ? index + 1 : index;
    }

    private static bool IsInterpolatedStringStart(string text, int quoteIndex)
    {
        return quoteIndex > 1
            && text[quoteIndex - 1] == '!'
            && IsIdentifierContinuation(text[quoteIndex - 2]);
    }

    private static int SkipInterpolatedString(string text, int index)
    {
        while (index < text.Length)
        {
            if (text[index] == '\\' && index + 1 < text.Length)
            {
                index += 2;
            }
            else if (text[index] == '"')
            {
                return index + 1;
            }
            else if (text[index] == '{')
            {
                index = SkipInterpolationExpression(text, index + 1);
            }
            else
            {
                index++;
            }
        }

        return index;
    }

    private static int SkipInterpolationExpression(string text, int index)
    {
        var braceDepth = 1;
        while (index < text.Length && braceDepth > 0)
        {
            var current = text[index];
            var next = index + 1 < text.Length ? text[index + 1] : '\0';

            if (current == '-' && next == '-')
            {
                index = SkipLineComment(text, index + 2);
            }
            else if (current == '/' && next == '-')
            {
                index = SkipBlockComment(text, index + 2);
            }
            else if (TrySkipRawString(text, index, out var rawStringEnd))
            {
                index = rawStringEnd;
            }
            else if (current == '\'' && IsCharacterLiteralStart(text, index))
            {
                index = SkipCharacterLiteral(text, index + 1);
            }
            else if (current == '«')
            {
                index = SkipGuillemetIdentifier(text, index + 1);
            }
            else if (current == '"')
            {
                index = IsInterpolatedStringStart(text, index)
                    ? SkipInterpolatedString(text, index + 1)
                    : SkipQuoted(text, index + 1, '"');
            }
            else if (current == '{')
            {
                braceDepth++;
                index++;
            }
            else if (current == '}')
            {
                braceDepth--;
                index++;
            }
            else
            {
                index++;
            }
        }

        return index;
    }
}
