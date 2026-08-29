using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace StrataLint.Engine;

internal sealed record LeanSourceDeclaration(
    RepoPath Path,
    string FullName,
    string Kind,
    bool IsProof,
    ImmutableArray<LeanSourceToken> SemanticTokens,
    ImmutableArray<LeanSourceToken> AmbientTokens,
    ImmutableArray<string> Imports,
    ImmutableHashSet<string> CustomSyntaxLiterals);

internal sealed record LeanSourceScope(string? NamespaceName);

internal sealed class LeanSourceCatalog
{
    private static readonly ImmutableHashSet<string> DeclarationKinds =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "theorem",
            "lemma",
            "def",
            "abbrev",
            "opaque",
            "axiom",
            "inductive",
            "structure",
            "class",
            "instance",
            "constant");
    private static readonly ImmutableHashSet<string> ProofKinds =
        ImmutableHashSet.Create(StringComparer.Ordinal, "theorem", "lemma");
    private static readonly ImmutableHashSet<string> ReservedIdentifiers =
        DeclarationKinds
            .Concat(
            [
                "by", "where", "let", "in", "if", "then", "else", "match", "with",
                "fun", "forall", "namespace", "end", "open", "private", "protected",
                "noncomputable", "partial", "unsafe", "mutual", "deriving", "extends",
            ])
            .ToImmutableHashSet(StringComparer.Ordinal);

    private readonly ImmutableArray<LeanSourceDeclaration> declarations;
    private readonly ImmutableDictionary<string, ImmutableArray<LeanSourceDeclaration>> byFullName;
    private readonly ImmutableDictionary<string, ImmutableArray<LeanSourceDeclaration>> byLeafName;
    private readonly ImmutableDictionary<string, ImmutableArray<string>> importsByModule;
    private readonly LeanCustomSyntaxCatalog customSyntaxCatalog;

    private LeanSourceCatalog(
        ImmutableArray<LeanSourceDeclaration> declarations,
        ImmutableDictionary<string, ImmutableArray<string>> importsByModule,
        ImmutableDictionary<string, ImmutableHashSet<string>> customSyntaxByModule)
    {
        this.declarations = declarations;
        this.importsByModule = importsByModule;
        customSyntaxCatalog = new LeanCustomSyntaxCatalog(
            importsByModule,
            customSyntaxByModule);
        byFullName = declarations
            .GroupBy(static declaration => declaration.FullName, StringComparer.Ordinal)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group.ToImmutableArray(),
                StringComparer.Ordinal);
        byLeafName = declarations
            .GroupBy(static declaration => LeafName(declaration.FullName), StringComparer.Ordinal)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group.ToImmutableArray(),
                StringComparer.Ordinal);
    }

    internal static LeanSourceCatalog Parse(RepositorySnapshot snapshot)
    {
        var declarations = ImmutableArray.CreateBuilder<LeanSourceDeclaration>();
        var importsByModule = ImmutableDictionary.CreateBuilder<
            string,
            ImmutableArray<string>>(StringComparer.Ordinal);
        var customSyntaxByModule = ImmutableDictionary.CreateBuilder<
            string,
            ImmutableHashSet<string>>(StringComparer.Ordinal);
        foreach (var file in snapshot.Files.Values
            .Where(static file => LeanClosureValidator.IsManagedLean(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
        {
            declarations.AddRange(ParseFile(file, out var imports, out var customSyntax));
            var moduleName = ModuleName(file.Path);
            importsByModule.Add(moduleName, imports);
            customSyntaxByModule.Add(moduleName, customSyntax);
        }

        return new LeanSourceCatalog(
            declarations.ToImmutable(),
            importsByModule.ToImmutable(),
            customSyntaxByModule.ToImmutable());
    }

    internal ImmutableArray<byte> ExtractPropositionSource(
        RepoPath modulePath,
        ImmutableArray<FrozenDeclarationStatement> recordedDeclarations)
    {
        var moduleDeclarations = declarations
            .Where(declaration => declaration.Path == modulePath)
            .ToImmutableArray();
        if (moduleDeclarations.IsEmpty || recordedDeclarations.IsDefaultOrEmpty)
        {
            throw new LeanSourceExtractionException(
                $"Lean proposition source is unavailable for {modulePath.Value}.");
        }

        var roots = ImmutableArray.CreateBuilder<(FrozenDeclarationStatement Recorded, LeanSourceDeclaration Source)>();
        foreach (var recorded in recordedDeclarations)
        {
            roots.Add((recorded, ResolveRecordedDeclaration(moduleDeclarations, recorded)));
        }

        var dependencies = new Dictionary<string, LeanSourceDeclaration>(StringComparer.Ordinal);
        var queue = new Queue<LeanSourceDeclaration>(roots.Select(static root => root.Source));
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var declaration))
        {
            var identity = declaration.Path.Value + "\0" + declaration.FullName;
            if (!visited.Add(identity))
            {
                continue;
            }

            RejectCustomSyntaxDependency(declaration);
            foreach (var dependency in ResolveDependencies(declaration))
            {
                if (dependency.IsProof)
                {
                    continue;
                }

                dependencies.TryAdd(
                    dependency.Path.Value + "\0" + dependency.FullName,
                    dependency);
                queue.Enqueue(dependency);
            }
        }

        var output = new StringBuilder();
        foreach (var root in roots.OrderBy(
            static root => root.Recorded.DeclarationNameKey,
            StringComparer.Ordinal))
        {
            AppendField(output, "root-key", root.Recorded.DeclarationNameKey);
            AppendField(output, "root-kind", root.Recorded.Kind);
            AppendField(output, "root-name", root.Source.FullName);
            AppendTokens(output, root.Source.AmbientTokens);
            AppendTokens(output, root.Source.SemanticTokens);
        }

        foreach (var dependency in dependencies.Values.OrderBy(
            static dependency => dependency.Path.Value + "\0" + dependency.FullName,
            StringComparer.Ordinal))
        {
            AppendField(output, "dependency-path", dependency.Path.Value);
            AppendField(output, "dependency-name", dependency.FullName);
            AppendField(output, "dependency-kind", dependency.Kind);
            AppendTokens(output, dependency.AmbientTokens);
            AppendTokens(output, dependency.SemanticTokens);
        }

        return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(output.ToString()));
    }

    private static LeanSourceDeclaration ResolveRecordedDeclaration(
        ImmutableArray<LeanSourceDeclaration> moduleDeclarations,
        FrozenDeclarationStatement recorded)
    {
        var recordedSegments = DecodeNameKey(recorded.DeclarationNameKey);
        if (recordedSegments.IsEmpty)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration name key cannot be resolved: {recorded.DeclarationNameKey}.");
        }

        var matches = moduleDeclarations
            .Where(declaration => NameKeyCanReferTo(recordedSegments, declaration.FullName))
            .OrderByDescending(static declaration => declaration.FullName.Length)
            .ToImmutableArray();
        if (matches.IsEmpty)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration source cannot be resolved: {recorded.DeclarationNameKey}.");
        }

        var bestLength = matches[0].FullName.Length;
        var best = matches.Where(declaration => declaration.FullName.Length == bestLength)
            .ToImmutableArray();
        if (best.Length != 1)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration source is ambiguous: {recorded.DeclarationNameKey}.");
        }

        var selected = best[0];
        if (!string.Equals(selected.Kind, recorded.Kind, StringComparison.Ordinal)
            && FullNameSegments(selected.FullName).Length == recordedSegments.Length)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration kind does not match source for {recorded.DeclarationNameKey}.");
        }

        return selected;
    }

    private IEnumerable<LeanSourceDeclaration> ResolveDependencies(
        LeanSourceDeclaration declaration)
    {
        var bound = BoundIdentifiers(declaration.SemanticTokens);
        foreach (var name in QualifiedIdentifiers(declaration.SemanticTokens)
            .Where(name => !bound.Contains(name) && !ReservedIdentifiers.Contains(name))
            .Distinct(StringComparer.Ordinal))
        {
            var candidates = ResolveDependencyCandidates(declaration, name);
            if (candidates.Length == 1)
            {
                if (candidates[0].Path != declaration.Path
                    && !IsImported(declaration, candidates[0]))
                {
                    throw new LeanSourceExtractionException(
                        $"Repository Lean dependency {name} is not imported by {declaration.FullName}.");
                }

                yield return candidates[0];
                continue;
            }

            if (candidates.Length > 1
                || name.StartsWith("D5.", StringComparison.Ordinal)
                || byLeafName.ContainsKey(LeafName(name)))
            {
                throw new LeanSourceExtractionException(
                    $"Repository Lean dependency {name} is unresolved for {declaration.FullName}.");
            }
        }
    }

    private ImmutableArray<LeanSourceDeclaration> ResolveDependencyCandidates(
        LeanSourceDeclaration owner,
        string name)
    {
        var result = new Dictionary<string, LeanSourceDeclaration>(StringComparer.Ordinal);
        AddExact(name);
        var ownerNamespace = NamespaceName(owner.FullName);
        while (ownerNamespace.Length > 0)
        {
            AddExact(ownerNamespace + "." + name);
            ownerNamespace = NamespaceName(ownerNamespace);
        }

        foreach (var local in declarations.Where(declaration =>
            declaration.Path == owner.Path
            && LeafName(declaration.FullName) == LeafName(name)))
        {
            result.TryAdd(local.Path.Value + "\0" + local.FullName, local);
        }

        if (byLeafName.TryGetValue(LeafName(name), out var leafMatches))
        {
            foreach (var match in leafMatches.Where(declaration => IsImported(owner, declaration)))
            {
                result.TryAdd(match.Path.Value + "\0" + match.FullName, match);
            }
        }

        return result.Values.ToImmutableArray();

        void AddExact(string fullName)
        {
            if (!byFullName.TryGetValue(fullName, out var matches))
            {
                return;
            }

            foreach (var match in matches)
            {
                result.TryAdd(match.Path.Value + "\0" + match.FullName, match);
            }
        }
    }

    private bool IsImported(
        LeanSourceDeclaration owner,
        LeanSourceDeclaration dependency)
    {
        if (owner.Path == dependency.Path)
        {
            return true;
        }

        var targetModule = ModuleName(dependency.Path);
        var queue = new Queue<string>(owner.Imports);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var imported))
        {
            if (!visited.Add(imported))
            {
                continue;
            }

            if (string.Equals(imported, targetModule, StringComparison.Ordinal))
            {
                return true;
            }

            if (importsByModule.TryGetValue(imported, out var transitive))
            {
                foreach (var next in transitive)
                {
                    queue.Enqueue(next);
                }
            }
        }

        return false;
    }

    private void RejectCustomSyntaxDependency(LeanSourceDeclaration declaration)
    {
        var semantic = declaration.SemanticTokens
            .Select(static token => LeanCustomSyntaxCatalog.NormalizeLiteral(token.Text))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var used = customSyntaxCatalog.VisibleFrom(declaration).FirstOrDefault(semantic.Contains);
        if (used is not null)
        {
            throw new LeanSourceExtractionException(
                $"Lean proposition source depends on unsupported custom syntax {used}.");
        }
    }

    private static ImmutableArray<LeanSourceDeclaration> ParseFile(
        RepositoryFile file,
        out ImmutableArray<string> imports,
        out ImmutableHashSet<string> customSyntax)
    {
        var tokens = LeanSourceTokenizer.Tokenize(file.Text);
        var commandStarts = FindCommandStarts(tokens);
        RejectIndentedDeclarations(tokens, commandStarts, file.Path);
        imports = ParseImports(tokens, commandStarts);
        customSyntax = LeanCustomSyntaxCatalog.ParseLiterals(tokens, commandStarts);
        var ambientTokens = ParseAmbientTokens(tokens, commandStarts);
        var scopeStack = new List<LeanSourceScope>();
        var result = ImmutableArray.CreateBuilder<LeanSourceDeclaration>();
        for (var commandIndex = 0; commandIndex < commandStarts.Length; commandIndex++)
        {
            var start = commandStarts[commandIndex];
            var end = commandIndex + 1 < commandStarts.Length
                ? commandStarts[commandIndex + 1]
                : tokens.Length;
            var command = tokens[start].Text;
            if (command == "namespace")
            {
                var namespaceName = ReadQualifiedName(tokens, start + 1, end);
                if (namespaceName.Length == 0)
                {
                    throw new LeanSourceExtractionException(
                        $"Lean namespace is malformed in {file.Path.Value}.");
                }

                scopeStack.Add(new LeanSourceScope(namespaceName));
                continue;
            }

            if (command == "section"
                || command == "mutual"
                || command == "noncomputable" && tokens[start..end].Any(static token =>
                    token.Text == "section"))
            {
                scopeStack.Add(new LeanSourceScope(null));
                continue;
            }

            if (command == "end")
            {
                if (scopeStack.Count == 0)
                {
                    throw new LeanSourceExtractionException(
                        $"Lean scope terminator is unmatched in {file.Path.Value}.");
                }

                scopeStack.RemoveAt(scopeStack.Count - 1);
                continue;
            }

            var kindIndex = FindDeclarationKind(tokens, start, end);
            if (kindIndex < 0)
            {
                continue;
            }

            var kind = tokens[kindIndex].Text;
            var nameIndex = NextIdentifier(tokens, kindIndex + 1, end);
            if (nameIndex < 0 || kind == "instance" && tokens[nameIndex].Text == "(")
            {
                continue;
            }

            var name = tokens[nameIndex].Text;
            var fullName = name.Contains('.', StringComparison.Ordinal)
                ? name
                : string.Join('.', scopeStack
                    .Select(static scope => scope.NamespaceName)
                    .Where(static namespaceName => namespaceName is not null)
                    .Append(name));
            var semanticEnd = end;
            if (ProofKinds.Contains(kind))
            {
                semanticEnd = FindProofStart(tokens, nameIndex + 1, end);
                if (semanticEnd < 0)
                {
                    throw new LeanSourceExtractionException(
                        $"Lean proof boundary is unresolved for {fullName}.");
                }
            }

            result.Add(new LeanSourceDeclaration(
                file.Path,
                fullName,
                kind,
                ProofKinds.Contains(kind),
                tokens[kindIndex..semanticEnd],
                ambientTokens,
                imports,
                customSyntax));
        }

        return result.ToImmutable();
    }

    private static ImmutableArray<int> FindCommandStarts(ImmutableArray<LeanSourceToken> tokens)
    {
        var result = ImmutableArray.CreateBuilder<int>();
        var mutualDepth = 0;
        for (var index = 0; index < tokens.Length; index++)
        {
            if (index > 0 && tokens[index - 1].Line == tokens[index].Line)
            {
                continue;
            }

            var text = tokens[index].Text;
            if ((tokens[index].Column == 0 || mutualDepth > 0)
                && (text is "@" or "import" or "namespace" or "end" or "section" or "mutual"
                or "macro" or "macro_rules" or "syntax" or "notation" or "local" or "scoped"
                or "elab" or "elab_rules" or "open" or "variable" or "include" or "omit"
                or "universe" or "set_option" or "attribute" or "export"
                || DeclarationKinds.Contains(text)
                || text is "private" or "protected" or "noncomputable" or "partial" or "unsafe"))
            {
                result.Add(index);
            }

            if (tokens[index].Column == 0 && text == "mutual")
            {
                mutualDepth++;
            }
            else if (tokens[index].Column == 0 && text == "end" && mutualDepth > 0)
            {
                mutualDepth--;
            }
        }

        return result.ToImmutable();
    }

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
                || token.Text == "constant"
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

    private static ImmutableArray<LeanSourceToken> ParseAmbientTokens(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableArray<int> commandStarts)
    {
        var result = ImmutableArray.CreateBuilder<LeanSourceToken>();
        for (var index = 0; index < commandStarts.Length; index++)
        {
            var start = commandStarts[index];
            var end = index + 1 < commandStarts.Length ? commandStarts[index + 1] : tokens.Length;
            if (FindDeclarationKind(tokens, start, end) < 0 && tokens[start].Text != "@")
            {
                result.AddRange(tokens[start..end]);
            }
        }

        return result.ToImmutable();
    }

    private static ImmutableArray<string> ParseImports(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableArray<int> commandStarts)
    {
        var result = ImmutableArray.CreateBuilder<string>();
        for (var index = 0; index < commandStarts.Length; index++)
        {
            var start = commandStarts[index];
            if (tokens[start].Text != "import")
            {
                continue;
            }

            var end = index + 1 < commandStarts.Length ? commandStarts[index + 1] : tokens.Length;
            for (var token = start + 1; token < end; token++)
            {
                if (IsIdentifier(tokens[token].Text))
                {
                    result.Add(tokens[token].Text);
                }
            }
        }

        return result.Distinct(StringComparer.Ordinal).ToImmutableArray();
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
            or "partial" or "unsafe" or "local"))
        {
            return -1;
        }

        for (var index = start + 1;
            index < end && tokens[index].Line == tokens[start].Line;
            index++)
        {
            if (DeclarationKinds.Contains(tokens[index].Text))
            {
                return index;
            }
        }

        return -1;
    }

    private static int NextIdentifier(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        int end)
    {
        for (var index = start; index < end; index++)
        {
            if (IsIdentifier(tokens[index].Text))
            {
                return index;
            }
        }

        return -1;
    }

    private static int FindProofStart(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        int end)
    {
        var depth = 0;
        for (var index = start; index < end; index++)
        {
            depth += tokens[index].Text switch
            {
                "(" or "[" or "{" => 1,
                ")" or "]" or "}" => -1,
                _ => 0,
            };
            if (depth == 0 && tokens[index].Text is ":=" or "where")
            {
                return index;
            }

            if (depth == 0
                && tokens[index].Text == "|"
                && (index == 0 || tokens[index - 1].Line < tokens[index].Line)
                && tokens[index..FirstTokenAfterLine(tokens, index)].Any(static token =>
                    token.Text == "=>"))
            {
                return index;
            }
        }

        return -1;
    }

    private static int FirstTokenAfterLine(
        ImmutableArray<LeanSourceToken> tokens,
        int start)
    {
        var line = tokens[start].Line;
        var index = start + 1;
        while (index < tokens.Length && tokens[index].Line == line)
        {
            index++;
        }

        return index;
    }

    private static string ReadQualifiedName(
        ImmutableArray<LeanSourceToken> tokens,
        int start,
        int end) =>
        start < end && IsIdentifier(tokens[start].Text) ? tokens[start].Text : string.Empty;

    private static ImmutableHashSet<string> BoundIdentifiers(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var result = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var signatureEnd = tokens.Length;
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
                signatureEnd = index;
                break;
            }
        }

        for (var index = 0; index < signatureEnd; index++)
        {
            if (tokens[index].Text is not ("(" or "{" or "["))
            {
                continue;
            }

            var close = tokens[index].Text switch { "(" => ")", "{" => "}", _ => "]" };
            for (var cursor = index + 1; cursor < tokens.Length && tokens[cursor].Text != close; cursor++)
            {
                if (tokens[cursor].Text == ":")
                {
                    break;
                }

                if (IsIdentifier(tokens[cursor].Text)
                    && !ReservedIdentifiers.Contains(tokens[cursor].Text))
                {
                    result.Add(tokens[cursor].Text);
                }
            }
        }

        return result.ToImmutable();
    }

    private static IEnumerable<string> QualifiedIdentifiers(
        ImmutableArray<LeanSourceToken> tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            if (!IsIdentifier(tokens[index].Text))
            {
                continue;
            }

            yield return tokens[index].Text;
        }
    }

    private static ImmutableArray<string> DecodeNameKey(string key)
    {
        var result = ImmutableArray.CreateBuilder<string>();
        for (var colon = 0; colon < key.Length; colon++)
        {
            if (key[colon] != ':')
            {
                continue;
            }

            var digitStart = colon - 1;
            while (digitStart >= 0 && char.IsAsciiDigit(key[digitStart]))
            {
                digitStart--;
            }

            digitStart++;
            if (digitStart == colon
                || !int.TryParse(
                    key.AsSpan(digitStart, colon - digitStart),
                    NumberStyles.None,
                    CultureInfo.InvariantCulture,
                    out var length)
                || length < 0
                || colon + 1 + length > key.Length)
            {
                throw new LeanSourceExtractionException("Lean declaration name key is malformed.");
            }

            result.Add(key.Substring(colon + 1, length));
            colon += length;
        }

        return result.ToImmutable();
    }

    private static bool NameKeyCanReferTo(
        ImmutableArray<string> recordedSegments,
        string fullName)
    {
        var sourceSegments = FullNameSegments(fullName);
        for (var start = 0; start + sourceSegments.Length <= recordedSegments.Length; start++)
        {
            if (sourceSegments.SequenceEqual(recordedSegments.Skip(start).Take(sourceSegments.Length)))
            {
                return true;
            }
        }

        return sourceSegments.Length == 1
            && recordedSegments.Contains(sourceSegments[0], StringComparer.Ordinal);
    }

    private static ImmutableArray<string> FullNameSegments(string fullName) =>
        fullName.Split('.', StringSplitOptions.RemoveEmptyEntries).ToImmutableArray();

    private static string ModuleName(RepoPath path) =>
        path.Value[..^".lean".Length].Replace('/', '.');

    private static bool IsIdentifier(string text) =>
        text.Length > 0 && IsIdentifierStart(text[0])
        && text.All(IsIdentifierPart);

    private static bool IsIdentifierStart(char value) =>
        value == '_' || char.IsLetter(value) || value > 127 && !char.IsWhiteSpace(value);

    private static bool IsIdentifierPart(char value) =>
        IsIdentifierStart(value) || char.IsDigit(value) || value == '\'' || value == '.';

    private static string NamespaceName(string fullName)
    {
        var separator = fullName.LastIndexOf('.');
        return separator < 0 ? string.Empty : fullName[..separator];
    }

    private static string LeafName(string fullName)
    {
        var separator = fullName.LastIndexOf('.');
        return separator < 0 ? fullName : fullName[(separator + 1)..];
    }

    private static void AppendTokens(
        StringBuilder output,
        ImmutableArray<LeanSourceToken> tokens) =>
        AppendField(output, "tokens", string.Join('\u001f', tokens.Select(static token => token.Text)));

    private static void AppendField(StringBuilder output, string name, string value) =>
        output.Append(name.Length).Append(':').Append(name)
            .Append(value.Length).Append(':').Append(value).Append('\n');
}
