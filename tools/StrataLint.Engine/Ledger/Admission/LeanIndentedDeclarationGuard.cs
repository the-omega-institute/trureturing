using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private static readonly ImmutableHashSet<string> BinderKeywords =
        ImmutableHashSet.Create(StringComparer.Ordinal, "forall", "∀", "fun", "exists", "∃");
    private static readonly ImmutableHashSet<string> BigBinderTokens =
        ImmutableHashSet.Create(StringComparer.Ordinal, "∑", "∏", "⋃", "⋂");

    private static bool IsBoundIdentifier(
        string name,
        ImmutableHashSet<string> bound)
    {
        return bound.Contains(name)
            || bound.Contains(LeanSourceTokenizer.IdentifierText(FullNameSegments(name).Take(1)));
    }

    private static ImmutableHashSet<string> BoundIdentifiers(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var result = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var signatureEnd = FindSignatureColon(tokens);
        for (var index = 0; index < signatureEnd; index++)
        {
            if (tokens[index].Text is "(" or "{" or "[")
            {
                AddDelimitedBinder(tokens, index, signatureEnd, result);
            }
        }

        for (var index = signatureEnd + 1; index < tokens.Length; index++)
        {
            if (BinderKeywords.Contains(tokens[index].Text))
            {
                AddKeywordBinders(tokens, index + 1, result);
            }
            else if (tokens[index].Text == "let")
            {
                AddFirstIdentifier(tokens, index + 1, ":=", result);
            }
            else if (BigBinderTokens.Contains(tokens[index].Text.TrimEnd('\'')))
            {
                AddFirstIdentifier(tokens, index + 1, ",", result);
            }
            else if (tokens[index].Text == "{")
            {
                AddSetBinder(tokens, index, result);
            }
        }

        AddWhereBinders(tokens, result);
        AddTacticBinders(tokens, result);

        return result.ToImmutable();
    }

    private static void AddWhereBinders(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableHashSet<string>.Builder result)
    {
        var where = -1;
        for (var index = 0; index < tokens.Length; index++)
        {
            if (tokens[index].Text == "where")
            {
                where = index;
                break;
            }
        }
        if (where < 0)
        {
            return;
        }

        for (var start = where + 1; start < tokens.Length; start++)
        {
            if (start > 0 && tokens[start - 1].Line == tokens[start].Line)
            {
                continue;
            }

            var end = FirstTokenAfterLine(tokens, start);
            var separator = -1;
            for (var index = start + 1; index < end; index++)
            {
                if (tokens[index].Text is ":" or ":=")
                {
                    separator = index;
                    break;
                }
            }

            if (separator < 0)
            {
                continue;
            }

            if (tokens[separator].Text == ":")
            {
                AddIdentifier(tokens[start], result);
                continue;
            }

            for (var index = start + 1; index < separator; index++)
            {
                AddIdentifier(tokens[index], result);
            }
        }
    }

    private static void AddTacticBinders(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableHashSet<string>.Builder result)
    {
        for (var start = 0; start < tokens.Length; start++)
        {
            if (start > 0 && tokens[start - 1].Line == tokens[start].Line)
            {
                continue;
            }

            var command = tokens[start].Text;
            if (command is not ("intro" or "rintro" or "ext" or "funext"))
            {
                continue;
            }

            var end = FirstTokenAfterLine(tokens, start);
            for (var index = start + 1; index < end; index++)
            {
                AddIdentifier(tokens[index], result);
            }
        }
    }

    private static int FindSignatureColon(ImmutableArray<LeanSourceToken> tokens)
    {
        var depth = 0;
        for (var index = 0; index < tokens.Length; index++)
        {
            depth += tokens[index].Text switch
            {
                "(" or "[" or "{" => 1,
                ")" or "]" or "}" => -1,
                _ => 0,
            };
            if (depth == 0 && tokens[index].Text == ":")
            {
                return index;
            }
        }

        return tokens.Length;
    }

    private static void AddKeywordBinders(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        ImmutableHashSet<string>.Builder result)
    {
        for (var index = start; index < tokens.Length; index++)
        {
            if (tokens[index].Text is "," or "=>")
            {
                return;
            }

            if (tokens[index].Text is "(" or "{" or "[")
            {
                index = AddDelimitedBinder(tokens, index, tokens.Length, result);
                continue;
            }

            if (tokens[index].Text == ":")
            {
                SkipToBinderTerminator(tokens, ref index);
                return;
            }

            AddIdentifier(tokens[index], result);
        }
    }

    private static int AddDelimitedBinder(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        int limit,
        ImmutableHashSet<string>.Builder result)
    {
        var close = tokens[start].Text switch { "(" => ")", "{" => "}", _ => "]" };
        var depth = 1;
        var colon = -1;
        var end = start + 1;
        for (; end < limit && depth > 0; end++)
        {
            if (depth == 1 && tokens[end].Text == ":")
            {
                colon = end;
            }

            depth += tokens[end].Text == tokens[start].Text ? 1 : tokens[end].Text == close ? -1 : 0;
        }

        if (colon > start)
        {
            for (var index = start + 1; index < colon; index++)
            {
                AddIdentifier(tokens[index], result);
            }
        }

        return Math.Max(start, end - 1);
    }

    private static void AddSetBinder(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        ImmutableHashSet<string>.Builder result)
    {
        var pipe = start + 1;
        while (pipe < tokens.Length && tokens[pipe].Text is not ("|" or "}"))
        {
            pipe++;
        }

        if (pipe < tokens.Length && tokens[pipe].Text == "|")
        {
            var colon = Enumerable.Range(start + 1, pipe - start - 1)
                .FirstOrDefault(index => tokens[index].Text == ":", pipe);
            for (var index = start + 1; index < colon; index++)
            {
                AddIdentifier(tokens[index], result);
            }
        }
    }

    private static void AddFirstIdentifier(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        string terminator,
        ImmutableHashSet<string>.Builder result)
    {
        for (var index = start; index < tokens.Length && tokens[index].Text != terminator; index++)
        {
            if (tokens[index].IsIdentifier)
            {
                result.Add(tokens[index].Identifier);
                return;
            }
        }
    }

    private static void AddIdentifier(
        LeanSourceToken token,
        ImmutableHashSet<string>.Builder result)
    {
        if (token.IsIdentifier && !ReservedIdentifiers.Contains(token.Text))
        {
            result.Add(token.Identifier);
        }
    }

    private static void SkipToBinderTerminator(
        ImmutableArray<LeanSourceToken> tokens,
        ref int index)
    {
        var depth = 0;
        while (++index < tokens.Length)
        {
            depth += tokens[index].Text switch
            {
                "(" or "[" or "{" => 1,
                ")" or "]" or "}" => -1,
                _ => 0,
            };
            if (depth == 0 && tokens[index].Text is "," or "=>")
            {
                return;
            }
        }
    }

    private static ImmutableArray<string> DecodeNameKey(string key)
    {
        var result = ImmutableArray.CreateBuilder<string>();
        var index = 0;
        if (!TryDecodeNameKeyNode(key, ref index, result) || index != key.Length)
        {
            throw new LeanSourceExtractionException("Lean declaration name key is malformed.");
        }

        return result.ToImmutable();
    }

    private static bool TryDecodeNameKeyNode(
        string key,
        ref int index,
        ImmutableArray<string>.Builder result)
    {
        if (key.AsSpan(index).StartsWith("n0", StringComparison.Ordinal))
        {
            index += 2;
            return true;
        }

        var isString = key.AsSpan(index).StartsWith("ns(", StringComparison.Ordinal);
        var isNumeric = key.AsSpan(index).StartsWith("nn(", StringComparison.Ordinal);
        if (!isString && !isNumeric)
        {
            return false;
        }

        index += 3;
        if (!TryDecodeNameKeyNode(key, ref index, result)
            || index >= key.Length
            || key[index++] != ',')
        {
            return false;
        }

        var digitStart = index;
        while (index < key.Length && char.IsAsciiDigit(key[index]))
        {
            index++;
        }
        if (digitStart == index)
        {
            return false;
        }

        if (isString)
        {
            if (index >= key.Length
                || key[index++] != ':'
                || !int.TryParse(
                    key.AsSpan(digitStart, index - digitStart - 1),
                    NumberStyles.None,
                    CultureInfo.InvariantCulture,
                    out var byteLength)
                || !TryReadUtf8Segment(key, ref index, byteLength, out var segment))
            {
                return false;
            }

            result.Add(segment);
        }

        return index < key.Length && key[index++] == ')';
    }

    private static bool TryReadUtf8Segment(
        string key,
        ref int index,
        int byteLength,
        out string segment)
    {
        var start = index;
        var bytes = 0;
        while (bytes < byteLength && index < key.Length)
        {
            var rune = Rune.GetRuneAt(key, index);
            bytes += rune.Utf8SequenceLength;
            index += rune.Utf16SequenceLength;
        }

        segment = bytes == byteLength ? key[start..index] : string.Empty;
        return bytes == byteLength;
    }

    private static bool IsCompilerGeneratedName(ImmutableArray<string> segments) =>
        segments.Any(segment =>
        {
            var leaf = LeafName(segment);
            return segment.StartsWith("term", StringComparison.Ordinal)
                || segment.StartsWith("_aux_", StringComparison.Ordinal)
                || leaf.StartsWith("inst", StringComparison.Ordinal)
                || leaf.StartsWith("_aux_", StringComparison.Ordinal)
                || leaf.StartsWith("term", StringComparison.Ordinal)
                || leaf.StartsWith("match_", StringComparison.Ordinal)
                || leaf.EndsWith("_getElem?", StringComparison.Ordinal)
                || leaf is "congr_simp" or "splitter";
        });

    private static LeanSourceDeclaration CreateGeneratorClosure(
        ImmutableArray<LeanSourceDeclaration> moduleDeclarations,
        string recordedKind)
    {
        var first = moduleDeclarations[0];
        var semantic = ImmutableArray.CreateBuilder<LeanSourceToken>();
        foreach (var declaration in moduleDeclarations)
        {
            semantic.AddRange(declaration.SemanticTokens);
        }

        return new LeanSourceDeclaration(
            first.Path,
            ModuleName(first.Path) + "._generated_source_closure",
            recordedKind,
            IsProof: false,
            semantic.ToImmutable(),
            first.AmbientTokens,
            first.Imports,
            first.CustomSyntaxLiterals);
    }

    private static bool IsGeneratorClosure(LeanSourceDeclaration declaration) =>
        declaration.FullName.EndsWith("._generated_source_closure", StringComparison.Ordinal);
}
