using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal abstract record TaskBlockScanResult
{
    internal sealed record Exact(int Count) : TaskBlockScanResult;

    internal sealed record Ambiguous(int CharacterIndex, string Reason) : TaskBlockScanResult;
}

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

    internal static TaskBlockScanResult ScanDocumentationCommentTaskStarts(
        string text,
        string caseId)
    {
        ArgumentNullException.ThrowIfNull(text);
        ArgumentException.ThrowIfNullOrWhiteSpace(caseId);

        var starts = new HashSet<int>();

        // This is lexical-state tracking only: it decides whether a /-- opener is active,
        // not whether the surrounding Lean parses. The pinned v4.31.0 states that can make
        // /-, -/, --, or " bytes inert are comments, quoted strings/chars, raw strings,
        // guillemet identifiers, and interpolated-string literal chunks. Numerals, ordinary
        // identifiers, and other tokens do not change those bytes and are intentionally out of scope.
        // Ticket files with primed identifiers or literal introducers at an unprovable token
        // boundary intentionally fail closed. Ambiguity poisons the whole scan: later bytes are
        // never used to recover an Exact count.
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

            if (TryGetRawStringDelimiter(text, index, out var rawStringDelimiter))
            {
                if (!IsTokenStart(text, index))
                {
                    return Ambiguous(
                        index,
                        "raw string introducer does not begin at a provable token boundary");
                }

                index = SkipRawString(text, index, rawStringDelimiter);
                continue;
            }

            if (current == '\'')
            {
                if (!IsTokenStart(text, index))
                {
                    return Ambiguous(
                        index,
                        "apostrophe may belong to a primed identifier or a character literal");
                }

                if (!TrySkipCharacterLiteral(text, index + 1, out var characterLiteralEnd))
                {
                    return Ambiguous(index, "character literal entry cannot be classified exactly");
                }

                index = characterLiteralEnd;
                continue;
            }

            if (current == '«')
            {
                index = SkipGuillemetIdentifier(text, index + 1);
                continue;
            }

            if (current == '"')
            {
                if (IsInterpolatedStringCandidate(text, index))
                {
                    if (!IsProvableInterpolatedStringStart(text, index))
                    {
                        return Ambiguous(
                            index,
                            "interpolated string entry does not begin at a provable token boundary");
                    }

                    index = SkipInterpolatedString(
                        text,
                        index + 1,
                        out var interpolationAmbiguity);
                    if (interpolationAmbiguity is not null)
                    {
                        return interpolationAmbiguity;
                    }
                }
                else
                {
                    if (!IsTokenStart(text, index))
                    {
                        return Ambiguous(
                            index,
                            "quoted string entry does not begin at a provable token boundary");
                    }

                    index = SkipQuoted(text, index + 1, '"');
                }

                continue;
            }

            index++;
        }

        var count = DocumentationCommentTaskPattern.Matches(text)
            .Count(match => starts.Contains(match.Groups["open"].Index)
                && string.Equals(
                    match.Groups["code"].Value,
                    caseId,
                    StringComparison.Ordinal));
        return new TaskBlockScanResult.Exact(count);
    }

    private static TaskBlockScanResult.Ambiguous Ambiguous(int index, string reason) =>
        new(index, reason);

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

    private static bool TryGetRawStringDelimiter(string text, int index, out int delimiter)
    {
        delimiter = index;
        if (text[index] != 'r')
        {
            return false;
        }

        delimiter = index + 1;
        while (delimiter < text.Length && text[delimiter] == '#')
        {
            delimiter++;
        }

        if (delimiter >= text.Length || text[delimiter] != '"')
        {
            return false;
        }

        return true;
    }

    private static int SkipRawString(string text, int start, int delimiter)
    {
        var hashCount = delimiter - start - 1;
        var cursor = delimiter + 1;
        while (cursor < text.Length)
        {
            if (text[cursor] == '"' && HasClosingHashes(text, cursor + 1, hashCount))
            {
                return cursor + hashCount + 1;
            }

            cursor++;
        }

        return text.Length;
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

    private static bool TrySkipCharacterLiteral(string text, int index, out int end)
    {
        end = index;
        if (index >= text.Length)
        {
            return false;
        }

        if (text[index] == '\\')
        {
            index++;
            if (index >= text.Length)
            {
                return false;
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

        if (index < text.Length && text[index] == '\'')
        {
            end = index + 1;
            return true;
        }

        return false;
    }

    private static int SkipGuillemetIdentifier(string text, int index)
    {
        while (index < text.Length && text[index] != '»')
        {
            index++;
        }

        return index < text.Length ? index + 1 : index;
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

    private static bool IsInterpolatedStringCandidate(string text, int quoteIndex) =>
        quoteIndex > 0 && text[quoteIndex - 1] == '!';

    private static bool IsProvableInterpolatedStringStart(string text, int quoteIndex) =>
        quoteIndex >= 2
        && text[quoteIndex - 2] == 's'
        && IsTokenStart(text, quoteIndex - 2);

    private static int SkipInterpolatedString(
        string text,
        int index,
        out TaskBlockScanResult.Ambiguous? ambiguity)
    {
        ambiguity = null;
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
                index = SkipInterpolationExpression(text, index + 1, out ambiguity);
                if (ambiguity is not null)
                {
                    return text.Length;
                }
            }
            else
            {
                index++;
            }
        }

        return index;
    }

    private static int SkipInterpolationExpression(
        string text,
        int index,
        out TaskBlockScanResult.Ambiguous? ambiguity)
    {
        ambiguity = null;
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
            else if (TryGetRawStringDelimiter(text, index, out var rawStringDelimiter))
            {
                if (!IsTokenStart(text, index))
                {
                    ambiguity = Ambiguous(
                        index,
                        "raw string introducer does not begin at a provable token boundary");
                    return text.Length;
                }

                index = SkipRawString(text, index, rawStringDelimiter);
            }
            else if (current == '\'')
            {
                if (!IsTokenStart(text, index))
                {
                    ambiguity = Ambiguous(
                        index,
                        "apostrophe may belong to a primed identifier or a character literal");
                    return text.Length;
                }

                if (!TrySkipCharacterLiteral(text, index + 1, out var characterLiteralEnd))
                {
                    ambiguity = Ambiguous(
                        index,
                        "character literal entry cannot be classified exactly");
                    return text.Length;
                }

                index = characterLiteralEnd;
            }
            else if (current == '«')
            {
                index = SkipGuillemetIdentifier(text, index + 1);
            }
            else if (current == '"')
            {
                if (IsInterpolatedStringCandidate(text, index))
                {
                    if (!IsProvableInterpolatedStringStart(text, index))
                    {
                        ambiguity = Ambiguous(
                            index,
                            "interpolated string entry does not begin at a provable token boundary");
                        return text.Length;
                    }

                    index = SkipInterpolatedString(text, index + 1, out ambiguity);
                    if (ambiguity is not null)
                    {
                        return text.Length;
                    }
                }
                else
                {
                    if (!IsTokenStart(text, index))
                    {
                        ambiguity = Ambiguous(
                            index,
                            "quoted string entry does not begin at a provable token boundary");
                        return text.Length;
                    }

                    index = SkipQuoted(text, index + 1, '"');
                }
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
