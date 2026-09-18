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

    private static bool IsName(string text) => text.Length > 0 && (Identifier(text[0]) || text[0] == '«');
    private static bool Identifier(char c) => char.IsLetterOrDigit(c) || c is '_' or '\'' or '!' or '?'
        || char.GetUnicodeCategory(c) is UnicodeCategory.NonSpacingMark or UnicodeCategory.SpacingCombiningMark
            or UnicodeCategory.LetterNumber or UnicodeCategory.OtherNumber;

    private static IEnumerable<string> Tokens(string source)
    {
        var i = 0;
        while (i < source.Length)
        {
            if (char.IsWhiteSpace(source[i])) { i++; continue; }
            if (source.AsSpan(i).StartsWith("--", StringComparison.Ordinal))
            {
                while (i < source.Length && source[i] != '\n') i++;
                continue;
            }
            if (source.AsSpan(i).StartsWith("/-", StringComparison.Ordinal))
            {
                var nesting = 1;
                i += 2;
                while (i < source.Length && nesting > 0)
                {
                    if (source.AsSpan(i).StartsWith("/-", StringComparison.Ordinal)) { nesting++; i += 2; }
                    else if (source.AsSpan(i).StartsWith("-/", StringComparison.Ordinal)) { nesting--; i += 2; }
                    else i++;
                }
                if (nesting != 0) throw new FormatException("unterminated Lean comment in declaration-name source");
                continue;
            }
            if (source[i] == '"')
            {
                i++;
                while (i < source.Length && source[i] != '"') i += source[i] == '\\' ? 2 : 1;
                if (i >= source.Length) throw new FormatException("unterminated Lean string in declaration-name source");
                i++;
                continue;
            }
            if (source[i] == '\'' && i + 2 < source.Length)
            {
                if (source[i + 2] == '\'') { i += 3; continue; }
                if (source[i + 1] == '\\')
                {
                    var end = source.IndexOf('\'', i + 3);
                    if (end >= 0) { i = end + 1; continue; }
                }
            }
            if (Identifier(source[i]) || source[i] == '«')
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
                    else while (i < source.Length && Identifier(source[i])) name.Append(source[i++]);
                    if (i + 1 >= source.Length || source[i] != '.' || !(Identifier(source[i + 1]) || source[i + 1] == '«')) break;
                    name.Append(source[i++]);
                } while (i < source.Length);
                yield return name.ToString();
            }
            else yield return source[i++].ToString();
        }
    }
}
