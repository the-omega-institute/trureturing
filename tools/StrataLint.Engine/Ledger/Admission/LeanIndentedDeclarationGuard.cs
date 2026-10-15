using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace StrataLint.Engine;

// 缩进声明守卫:Lean 命令必须起于第 0 列,故任何【缩进行的首个 token】若看起来像
// 声明,就说明提取器读到了它无法忠实还原的形状,一律 fail-closed 拒绝 —— 它挡的是
// 「顶层陈述看着没变,却在缩进处偷加/偷改定义」这一类语义削弱。
internal sealed partial class LeanSourceCatalog
{
    private static readonly ImmutableHashSet<string> BinderKeywords =
        ImmutableHashSet.Create(StringComparer.Ordinal, "forall", "∀", "fun", "exists", "∃");
    private static readonly ImmutableHashSet<string> BigBinderTokens =
        ImmutableHashSet.Create(StringComparer.Ordinal, "∑", "∏", "⋃", "⋂");

    // Lean 标识符可含字母、数字、`_`、`'`、`?`、`!`、`.`(限定名)与 Unicode 字母;
    // 运算符与标点(`-`、`(`、`:`、`,` …)一律不是。判首字符即可区分本例。
    private static bool IsIdentifierToken(string text) =>
        text.Length > 0 && (char.IsLetter(text[0]) || text[0] == '_');

    private static void RejectIndentedDeclarations(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableArray<int> commandStarts,
        RepoPath path)
    {
        var recognized = commandStarts.ToImmutableHashSet();
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token.Column == 0
                || recognized.Contains(index)
                || index > 0 && tokens[index - 1].Line == token.Line)
            {
                continue;
            }

            if (token.Text == "@"
                && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                    candidate.Line == token.Line && DeclarationKinds.Contains(candidate.Text))
                || DeclarationKinds.Contains(token.Text) && token.Text != "constant"
                // `constant` 在 Lean 4 已不是声明关键字(被 `opaque` 取代)。实测
                // 4.31 与 4.33:`constant foo : Nat := 1` 均报
                // `unexpected identifier; expected command`,而
                // `def bar (constant : Nat) := constant - 0` 被接受。
                // 故仅当其后【紧跟标识符】时才可能是 Lean 3 遗留的声明形;
                // 紧跟运算符者是项,不是声明。本仓
                // D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.lean:98
                //     constant - (Fintype.card State : Real) * coefficient state action
                // 即此形:行内的 `:` 来自类型标注,旧判据据此误判为缩进声明,
                // 使整条 mathlib 升级授权路径恒 false。
                || token.Text == "constant"
                    && index + 1 < tokens.Length
                    && tokens[index + 1].Line == token.Line
                    && IsIdentifierToken(tokens[index + 1].Text)
                    && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                        candidate.Line == token.Line && candidate.Text == ":")
                || token.Text is "private" or "protected" or "noncomputable" or "partial" or "unsafe"
                    && tokens[index..Math.Min(tokens.Length, index + 32)].Any(candidate =>
                        candidate.Line == token.Line && DeclarationKinds.Contains(candidate.Text)))
            {
                throw new LeanSourceExtractionException(
                    $"Indented Lean declaration is unsupported in {path.Value}.");
            }
        }
    }

    private static bool IsBoundIdentifier(
        string name,
        ImmutableHashSet<string> bound)
    {
        var separator = name.IndexOf('.');
        return bound.Contains(name)
            || separator > 0 && bound.Contains(name[..separator]);
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
            else if (BigBinderTokens.Contains(tokens[index].Text))
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
                AddIdentifier(tokens[start].Text, result);
                continue;
            }

            for (var index = start + 1; index < separator; index++)
            {
                AddIdentifier(tokens[index].Text, result);
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
                AddIdentifier(tokens[index].Text, result);
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

            AddIdentifier(tokens[index].Text, result);
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
                AddIdentifier(tokens[index].Text, result);
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
                AddIdentifier(tokens[index].Text, result);
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
            if (IsIdentifier(tokens[index].Text))
            {
                result.Add(tokens[index].Text);
                return;
            }
        }
    }

    private static void AddIdentifier(
        string token,
        ImmutableHashSet<string>.Builder result)
    {
        if (IsIdentifier(token) && !ReservedIdentifiers.Contains(token))
        {
            result.Add(token);
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

    private static ImmutableArray<string> DecodeNameKey(string key) =>
        DecodeNameKeySegments(key).Where(static segment => !segment.IsNumeric)
            .Select(static segment => segment.Text).ToImmutableArray();

    private static ImmutableArray<(string Text, bool IsNumeric)> DecodeNameKeySegments(string key)
    {
        var result = ImmutableArray.CreateBuilder<(string Text, bool IsNumeric)>();
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
        ImmutableArray<(string Text, bool IsNumeric)>.Builder result)
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

            result.Add((segment, false));
        }
        else
        {
            result.Add((key[digitStart..index], true));
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

    private static bool IsCompilerGeneratedName(
        ImmutableArray<string> segments, ImmutableArray<LeanSourceDeclaration> moduleDeclarations)
    {
        var hasInstanceGenerator = moduleDeclarations.Any(static declaration =>
            declaration.IsAnonymousOnlySource
            || declaration.Kind is "inductive" or "structure" or "class"
            || declaration.SemanticTokens.Any(static token => token.Text == "deriving"))
            || AnonymousInstanceCommands(moduleDeclarations[0].AmbientTokens).Any()
            || GeneratorCommands(moduleDeclarations[0].AmbientTokens).Any();
        return segments.Any(segment =>
        {
            var leaf = LeafName(segment);
            return segment.StartsWith("term", StringComparison.Ordinal)
                || segment.StartsWith("_aux_", StringComparison.Ordinal)
                || hasInstanceGenerator && leaf.StartsWith("inst", StringComparison.Ordinal)
                || leaf.StartsWith("_aux_", StringComparison.Ordinal)
                || leaf.StartsWith("term", StringComparison.Ordinal)
                || leaf.StartsWith("match_", StringComparison.Ordinal)
                || leaf.EndsWith("_getElem?", StringComparison.Ordinal)
                || leaf is "congr_simp" or "splitter" or "eq_def"
                || leaf.EndsWith("_assoc", StringComparison.Ordinal);
        });
    }

    private static bool HasNamedGenerator(LeanSourceDeclaration source, string recordedKey) =>
        HasSourceBoundName(source, recordedKey, source.NamedGenerators);

    private static bool HasSourceBoundName(
        LeanSourceDeclaration source, string recordedKey, IEnumerable<string> generatedNames)
    {
        var name = DecodeNameKeySegments(recordedKey);
        if (name.IsEmpty) return false;
        if (name[0] == ("_private", false))
        {
            var module = FullNameSegments(ModuleName(source.Path));
            var counter = 1 + module.Length;
            if (name.Length <= counter + 1
                || !module.Select(static segment => (segment, false))
                    .SequenceEqual(name.Skip(1).Take(module.Length))
                || !name[counter].IsNumeric)
                return false;
            name = name[(counter + 1)..];
        }

        return name.All(static segment => !segment.IsNumeric)
            && generatedNames.Any(generated => FullNameSegments(generated)
                .SequenceEqual(name.Select(static segment => segment.Text)));
    }

    private static ImmutableArray<int> CommandDelimiterDepths(
        ImmutableArray<LeanSourceToken> tokens, ImmutableArray<int> starts)
    {
        var depths = ImmutableArray.CreateBuilder<int>(starts.Length);
        var depth = 0;
        for (var index = 0; index < tokens.Length; index++)
        {
            if (depths.Count < starts.Length && starts[depths.Count] == index) depths.Add(depth);
            depth += tokens[index].Text switch
            {
                "(" or "[" or "{" => 1,
                ")" or "]" or "}" => -1,
                _ => 0,
            };
        }
        return depths.ToImmutable();
    }

    private static bool IsPrivateNameKey(string key)
    {
        var name = DecodeNameKeySegments(key);
        return !name.IsEmpty && name[0] == ("_private", false);
    }

    private static bool HasPrivateDeclarationModifier(ImmutableArray<LeanSourceToken> tokens)
    {
        var depth = 0;
        foreach (var token in tokens)
        {
            if (token.Text is "[" or "(" or "{") depth++;
            else if (token.Text is "]" or ")" or "}") depth--;
            else if (depth == 0 && token.Text == "private") return true;
        }
        return false;
    }

    private static bool IsAttributePrefix(ImmutableArray<LeanSourceToken> tokens)
    {
        var index = 0;
        while (index + 1 < tokens.Length && tokens[index].Text == "@" && tokens[index + 1].Text == "[")
        {
            var depth = 1;
            index += 2;
            while (index < tokens.Length && depth > 0)
            {
                if (tokens[index].Text == "[") depth++;
                else if (tokens[index].Text == "]") depth--;
                index++;
            }
            if (depth != 0) return false;
        }
        return index > 0 && index == tokens.Length;
    }

    private static bool HasBareExtAttribute(ImmutableArray<LeanSourceToken> tokens) =>
        HasDeclarationAttribute(tokens, "ext", requireBare: true);

    private static bool HasInstanceAttribute(ImmutableArray<LeanSourceToken> tokens) =>
        HasDeclarationAttribute(tokens, "instance", requireBare: false);

    private static bool HasDeclarationAttribute(
        ImmutableArray<LeanSourceToken> tokens, string name, bool requireBare)
    {
        for (var index = 0; index + 1 < tokens.Length; index++)
        {
            if (tokens[index].Text != "@" || tokens[index + 1].Text != "[") continue;
            var depth = 1;
            var itemStart = true;
            for (index += 2; index < tokens.Length && depth > 0; index++)
            {
                var text = tokens[index].Text;
                if (text is "[" or "(" or "{") depth++;
                else if (text is "]" or ")" or "}") depth--;
                else if (depth == 1 && text == ",") itemStart = true;
                else if (depth == 1)
                {
                    if (itemStart && text is "local" or "scoped") continue;
                    if (itemStart && text == name && (!requireBare || index + 1 < tokens.Length
                        && tokens[index + 1].Text is "," or "]")) return true;
                    itemStart = false;
                }
            }
            index--;
        }
        return false;
    }

    private static string? NamedGeneratorName(ImmutableArray<LeanSourceToken> command)
    {
        var header = command.TakeWhile(static token => token.Text != "=>").ToImmutableArray();
        var kind = header.SkipWhile(static token => token.Text is "local" or "scoped" or "public" or "private")
            .FirstOrDefault()?.Text;
        if (kind is not ("notation" or "syntax" or "macro" or "elab")) return null;
        for (var index = 0; index + 4 < header.Length; index++)
            if (header[index].Text == "(" && header[index + 1].Text == "name"
                && header[index + 2].Text == ":=" && IsIdentifier(header[index + 3].Text)
                && header[index + 4].Text == ")")
                return header[index + 3].Text;
        return null;
    }

    private static string QualifySourceName(string name, IEnumerable<LeanSourceScope> scopeStack) =>
        name.StartsWith("_root_.", StringComparison.Ordinal)
            ? name["_root_.".Length..]
            : string.Join('.', scopeStack.Select(static scope => scope.NamespaceName)
                .Where(static namespaceName => namespaceName is not null).Append(name));

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

    private static int InstanceNameIndex(ImmutableArray<LeanSourceToken> tokens, int kindIndex, int end)
    {
        var next = kindIndex + 1;
        if (next + 2 < end && tokens[next].Text == "("
            && tokens[next + 1].Text == "priority" && tokens[next + 2].Text == ":=")
        {
            var depth = 1;
            next += 3;
            while (next < end && depth > 0)
            {
                if (tokens[next].Text == "(") depth++;
                else if (tokens[next].Text == ")") depth--;
                next++;
            }
            if (depth != 0) return -1;
        }
        return next < end && IsIdentifier(tokens[next].Text) ? next : -1;
    }

    private static bool IsNamedInstance(
        ImmutableArray<LeanSourceToken> tokens, int kindIndex, int end) =>
        kindIndex >= 0 && tokens[kindIndex].Text == "instance"
        && !IsAnonymousInstance(tokens, kindIndex, end);

    private static IEnumerable<ImmutableArray<LeanSourceToken>> NamedInstanceCommands(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var starts = FindCommandStarts(tokens);
        for (var index = 0; index < starts.Length; index++)
        {
            var start = starts[index];
            var end = index + 1 < starts.Length ? starts[index + 1] : tokens.Length;
            if (IsNamedInstance(tokens, FindDeclarationKind(tokens, start, end), end))
                yield return tokens[start..end];
        }
    }

    private static int FindDeclarationKind(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        int end)
    {
        if (DeclarationKinds.Contains(tokens[start].Text))
        {
            return start;
        }

        if (tokens[start].Text is not ("@" or "private" or "protected" or "noncomputable"
            or "partial" or "unsafe" or "local" or "scoped" or "public" or "meta"
            or "set_option" or "include" or "omit" or "open"))
        {
            return -1;
        }

        var depth = 0;
        var body = tokens[start].Text is not ("set_option" or "include" or "omit" or "open");
        for (var index = start + 1;
            index < end && tokens[index].Line == tokens[start].Line;
            index++)
        {
            var text = tokens[index].Text;
            depth += text switch
            {
                "(" or "[" or "{" => 1,
                ")" or "]" or "}" => -1,
                _ => 0,
            };
            if (depth == 0 && text == "in") body = true;
            if (depth == 0 && body && DeclarationKinds.Contains(text))
            {
                return index;
            }
        }

        return -1;
    }

}
