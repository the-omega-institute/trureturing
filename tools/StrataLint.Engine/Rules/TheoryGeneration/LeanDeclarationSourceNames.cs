using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

// A name-only lexical view of source bytes, never an execution of base code.
// Proof text, comments and strings cannot manufacture a historical declaration.
internal static class LeanDeclarationSourceNames
{
    internal static ImmutableDictionary<string, string> Read(string source)
    {
        var tokens = Tokens(source).ToArray();
        var names = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        var scopes = new Stack<string>();
        var currentNamespace = "";
        var depth = 0;
        for (var i = 0; i < tokens.Length; i++)
        {
            var token = tokens[i];
            if (token is "(" or "[" or "{") { depth++; continue; }
            if (token is ")" or "]" or "}") { depth--; continue; }
            if (depth != 0) continue;
            if (token == "namespace" && i + 1 < tokens.Length)
            {
                scopes.Push(currentNamespace);
                currentNamespace = Qualify(currentNamespace, tokens[++i]);
            }
            else if (token is "section" or "mutual") scopes.Push(currentNamespace);
            else if (token == "end" && scopes.TryPop(out var previous)) currentNamespace = previous;
            else if (token is "theorem" or "lemma" or "def" or "instance" or "abbrev" or "structure"
                && i + 1 < tokens.Length && IsName(tokens[i + 1]))
                names[Qualify(currentNamespace, tokens[++i])] = token;
        }
        return names.ToImmutable();
    }

    private static string Qualify(string prefix, string name)
    {
        var qualified = name.StartsWith("_root_.", StringComparison.Ordinal)
            ? name[7..] : prefix.Length == 0 ? name : prefix + "." + name;
        return Regex.Replace(qualified, "«([^»]*)»", match => InformationTemplateJson.PlainIdentifier(match.Groups[1].Value)
            ? match.Groups[1].Value : match.Value);
    }

    private static bool IsName(string text) => text.Length > 0 && (IdentifierSize(text, 0) > 0 || text[0] == '«');

    private static int IdentifierSize(string source, int index)
    {
        if (!Rune.TryGetRuneAt(source, index, out var rune)) return 0;
        return Rune.IsLetterOrDigit(rune) || rune.Value is '_' or '\'' or '!' or '?'
            || Rune.GetUnicodeCategory(rune) is UnicodeCategory.NonSpacingMark or UnicodeCategory.SpacingCombiningMark
                or UnicodeCategory.LetterNumber or UnicodeCategory.OtherNumber ? rune.Utf16SequenceLength : 0;
    }

    private static IEnumerable<string> Tokens(string source)
    {
        var i = 0;
        while (i < source.Length)
        {
            if (SkipIgnored(source, ref i)) continue;
            if (IdentifierSize(source, i) > 0 || source[i] == '«')
            {
                var name = new StringBuilder();
                do
                {
                    if (source[i] == '«')
                    {
                        var end = source.IndexOf('»', i + 1);
                        if (end < 0) throw new FormatException("unterminated Lean escaped identifier");
                        name.Append(source, i, end - i + 1);
                        i = end + 1;
                    }
                    else while (i < source.Length && IdentifierSize(source, i) is > 0 and var width)
                    {
                        name.Append(source, i, width);
                        i += width;
                    }
                    if (i + 1 >= source.Length || source[i] != '.' || !(IdentifierSize(source, i + 1) > 0 || source[i + 1] == '«')) break;
                    name.Append(source[i++]);
                } while (i < source.Length);
                yield return name.ToString();
            }
            else yield return source[i++].ToString();
        }
    }

    private static bool SkipIgnored(string source, ref int index)
    {
        if (char.IsWhiteSpace(source[index])) { index++; return true; }
        if (source.AsSpan(index).StartsWith("--", StringComparison.Ordinal))
        {
            while (index < source.Length && source[index] != '\n') index++;
            return true;
        }
        if (source.AsSpan(index).StartsWith("/-", StringComparison.Ordinal))
        {
            var nesting = 1;
            index += 2;
            while (index < source.Length && nesting > 0)
            {
                if (source.AsSpan(index).StartsWith("/-", StringComparison.Ordinal)) { nesting++; index += 2; }
                else if (source.AsSpan(index).StartsWith("-/", StringComparison.Ordinal)) { nesting--; index += 2; }
                else index++;
            }
            if (nesting != 0) throw new FormatException("unterminated Lean comment in declaration-name source");
            return true;
        }
        if (source[index] == 'r')
        {
            var quote = index + 1;
            while (quote < source.Length && source[quote] == '#') quote++;
            if (quote < source.Length && source[quote] == '"')
            {
                var delimiter = "\"" + source[(index + 1)..quote];
                var end = source.IndexOf(delimiter, quote + 1, StringComparison.Ordinal);
                if (end < 0) throw new FormatException("unterminated Lean raw string in declaration-name source");
                index = end + delimiter.Length;
                return true;
            }
        }
        var prefixEnd = index;
        while (prefixEnd < source.Length && IdentifierSize(source, prefixEnd) is > 0 and var width) prefixEnd += width;
        if (prefixEnd > index && prefixEnd < source.Length && source[prefixEnd - 1] == '!' && source[prefixEnd] == '"')
        {
            index = prefixEnd;
            SkipString(source, ref index, interpolated: true);
            return true;
        }
        if (source[index] == '"')
        {
            SkipString(source, ref index, interpolated: false);
            return true;
        }
        if (source[index] == '\'' && index + 2 < source.Length)
        {
            var width = Rune.GetRuneAt(source, index + 1).Utf16SequenceLength;
            if (index + width + 1 < source.Length && source[index + width + 1] == '\'')
            { index += width + 2; return true; }
            if (source[index + 1] == '\\')
            {
                var end = source.IndexOf('\'', index + 3);
                if (end >= 0) { index = end + 1; return true; }
            }
        }
        return false;
    }

    private static void SkipString(string source, ref int index, bool interpolated)
    {
        index++;
        while (index < source.Length)
        {
            var current = source[index++];
            if (current == '"') return;
            if (current == '\\') { index++; continue; }
            if (!interpolated || current != '{') continue;
            var braces = 1;
            while (index < source.Length && braces > 0)
            {
                if (SkipIgnored(source, ref index)) continue;
                if (source[index] == '{') braces++;
                else if (source[index] == '}') braces--;
                if (IdentifierSize(source, index) > 0)
                    while (index < source.Length && IdentifierSize(source, index) is > 0 and var width) index += width;
                else index++;
            }
            if (braces != 0) throw new FormatException("unterminated Lean interpolation in declaration-name source");
        }
        throw new FormatException("unterminated Lean string in declaration-name source");
    }
}
