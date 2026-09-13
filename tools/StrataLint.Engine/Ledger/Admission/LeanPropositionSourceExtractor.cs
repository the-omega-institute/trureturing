using System.Collections.Immutable;
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

internal sealed partial class LeanSourceCatalog
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

    private readonly RepositorySnapshot snapshot;
    private readonly LeanSourceContextInput context;
    private readonly string side;
    private readonly bool? equalityAlternative;
    private readonly string? sourceReference;
    private readonly List<LeanSourceDeclaration> declarations = [];
    private readonly HashSet<RepoPath> loaded = [];
    private readonly Dictionary<string, ImmutableArray<string>> importsByModule = new(StringComparer.Ordinal);
    private readonly Dictionary<string, ImmutableHashSet<string>> customSyntaxByModule = new(StringComparer.Ordinal);

    private LeanSourceCatalog(RepositorySnapshot snapshot, LeanSourceContextInput context,
        string side, bool? equalityAlternative, string? sourceReference)
    {
        this.snapshot = snapshot;
        this.context = context;
        this.side = side;
        this.equalityAlternative = equalityAlternative;
        this.sourceReference = sourceReference;
    }

    internal static LeanSourceCatalog Parse(RepositorySnapshot snapshot,
        LeanSourceContextInput? context = null, string side = "current", bool? equalityAlternative = null, string? sourceReference = null) =>
        new(snapshot, context ?? LeanSourceContextInput.Empty, side, equalityAlternative, sourceReference);

    private void EnsureFile(RepoPath path)
    {
        if (loaded.Contains(path)) return;
        if (!snapshot.Files.TryGetValue(path, out var file))
            throw new LeanSourceExtractionException($"Lean source is missing: {path.Value}.");
        var input = context.GetFile(snapshot, path, side);
        var equality = sourceReference is null || !file.Text.Contains("='", StringComparison.Ordinal) ? input : context.GetRegistration(snapshot, path, side, sourceReference);
        declarations.AddRange(ParseFile(file, input, equality, equalityAlternative, out var imports, out var syntax));
        importsByModule[ModuleName(path)] = imports;
        customSyntaxByModule[ModuleName(path)] = syntax;
        loaded.Add(path);
    }

    private IEnumerable<RepositoryFile> ImportedSources(LeanSourceDeclaration owner)
    {
        var queue = new Queue<string>(owner.Imports);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var module))
        {
            if (!visited.Add(module) || !snapshot.TryGetFile(module.Replace('.', '/') + ".lean", out var file)
                || !LeanClosureValidator.IsManagedLean(file.Path.Value))
                continue;
            if (!importsByModule.TryGetValue(module, out var imports))
                importsByModule[module] = imports = ParseFileImports(file);
            foreach (var dependency in imports) queue.Enqueue(dependency);
            yield return file;
        }
    }

    internal static ImmutableArray<string> ParseFileImports(RepositoryFile file)
    {
        ArgumentNullException.ThrowIfNull(file);

        return LeanSourceHeader.Read(file.Text).Imports.Select(import => import.Module)
            .Where(module => module != "Init").Distinct(StringComparer.Ordinal).ToImmutableArray();
    }

    internal ImmutableArray<byte> ExtractPropositionSource(
        RepoPath modulePath,
        ImmutableArray<FrozenDeclarationStatement> recordedDeclarations)
    {
        EnsureFile(modulePath);
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
        foreach (var root in roots
            .Where(static root => !IsGeneratorClosure(root.Source))
            .OrderBy(
            static root => root.Recorded.DeclarationNameKey,
            StringComparer.Ordinal))
        {
            AppendField(output, "root-key", root.Recorded.DeclarationNameKey);
            AppendField(output, "root-kind", root.Recorded.Kind);
            AppendField(output, "root-name", root.Source.FullName);
            AppendTokens(output, root.Source.AmbientTokens);
            AppendTokens(output, root.Source.SemanticTokens);
        }

        var generatorRoot = roots
            .Select(static root => root.Source)
            .FirstOrDefault(IsGeneratorClosure);
        if (generatorRoot is not null)
        {
            AppendField(output, "root-kind", "compiler-generated-source-closure");
            AppendField(output, "root-name", generatorRoot.FullName);
            AppendTokens(output, generatorRoot.AmbientTokens);
            AppendTokens(output, generatorRoot.SemanticTokens);
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
            if (IsCompilerGeneratedName(recordedSegments))
            {
                return CreateGeneratorClosure(moduleDeclarations, recorded.Kind);
            }

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
        if (!RecordedKindMatchesSource(recorded.Kind, selected.Kind)
            && FullNameSegments(selected.FullName).Length == recordedSegments.Length)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration kind does not match source for {recorded.DeclarationNameKey}.");
        }

        return selected;
    }

    private static bool RecordedKindMatchesSource(string recordedKind, string sourceKind) =>
        string.Equals(recordedKind, sourceKind, StringComparison.Ordinal)
        || sourceKind switch
        {
            "structure" => recordedKind == "inductive",
            "abbrev" => recordedKind == "def",
            "instance" => recordedKind is "def" or "theorem",
            _ => false,
        };

    private IEnumerable<LeanSourceDeclaration> ResolveDependencies(
        LeanSourceDeclaration declaration)
    {
        if (IsGeneratorClosure(declaration))
        {
            foreach (var source in declarations.Where(source => source.Path == declaration.Path).ToArray())
            {
                foreach (var dependency in ResolveDependencies(source))
                {
                    yield return dependency;
                }
            }

            yield break;
        }

        var bound = BoundIdentifiers(declaration.SemanticTokens);
        foreach (var name in QualifiedIdentifiers(declaration.SemanticTokens)
            .Where(name => !IsBoundIdentifier(name, bound))
            .Distinct(StringComparer.Ordinal))
        {
            var candidates = ResolveDependencyCandidates(declaration, name);
            if (candidates.Length > 0)
            {
                foreach (var candidate in candidates)
                {
                    yield return candidate;
                }

                continue;
            }

            if (name.StartsWith("D5.", StringComparison.Ordinal))
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
        // This is only a spelling prefilter for demanded dependency candidates.
        // Compiler command spans still decide whether an occurrence is a declaration.
        var leaf = FullNameSegments(name).LastOrDefault() ?? name;
        foreach (var source in ImportedSources(owner).Where(file =>
            file.Text.Contains(leaf, StringComparison.Ordinal)).ToArray()) EnsureFile(source.Path);
        var byFullName = declarations.GroupBy(declaration => declaration.FullName, StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.ToImmutableArray(), StringComparer.Ordinal);
        var byLeafName = declarations.GroupBy(declaration => LeafName(declaration.FullName), StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.ToImmutableArray(), StringComparer.Ordinal);
        var result = new Dictionary<string, LeanSourceDeclaration>(StringComparer.Ordinal);
        foreach (var lookupName in DependencyLookupNames(name))
        {
            AddExact(lookupName);
            var ownerNamespace = NamespaceName(owner.FullName);
            while (ownerNamespace.Length > 0)
            {
                AddExact(ownerNamespace + "." + lookupName);
                ownerNamespace = NamespaceName(ownerNamespace);
            }

            foreach (var local in declarations.Where(declaration =>
                declaration.Path == owner.Path
                && LeafName(declaration.FullName) == LeafName(lookupName)))
            {
                result.TryAdd(local.Path.Value + "\0" + local.FullName, local);
            }

            if (byLeafName.TryGetValue(LeafName(lookupName), out var leafMatches))
            {
                foreach (var match in leafMatches.Where(declaration => IsImported(owner, declaration)))
                {
                    result.TryAdd(match.Path.Value + "\0" + match.FullName, match);
                }
            }
        }

        return result.Values.ToImmutableArray();

        void AddExact(string fullName)
        {
            if (!byFullName.TryGetValue(fullName, out var matches))
            {
                return;
            }

            foreach (var match in matches.Where(declaration =>
                declaration.Path == owner.Path || IsImported(owner, declaration)))
            {
                result.TryAdd(match.Path.Value + "\0" + match.FullName, match);
            }
        }
    }

    private static IEnumerable<string> DependencyLookupNames(string name)
    {
        yield return name;
        if (name.EndsWith('ˣ'))
        {
            yield return name[..^1];
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
        if (IsGeneratorClosure(declaration))
        {
            foreach (var source in declarations.Where(source => source.Path == declaration.Path).ToArray())
            {
                RejectCustomSyntaxDependency(source);
            }

            return;
        }

        var semantic = declaration.SemanticTokens
            .Select(static token => LeanCustomSyntaxCatalog.NormalizeLiteral(token.Text))
            .ToImmutableHashSet(StringComparer.Ordinal);
        foreach (var source in ImportedSources(declaration).Where(file => semantic.Any(atom =>
            file.Text.Contains("\"" + atom + "\"", StringComparison.Ordinal))).ToArray()) EnsureFile(source.Path);
        var customSyntaxCatalog = new LeanCustomSyntaxCatalog(importsByModule.ToImmutableDictionary(),
            customSyntaxByModule.ToImmutableDictionary());
        var used = customSyntaxCatalog.VisibleFrom(declaration).FirstOrDefault(semantic.Contains);
        if (used is not null)
        {
            throw new LeanSourceExtractionException(
                $"Lean proposition source depends on unsupported custom syntax {used}.");
        }
    }

    private static ImmutableArray<LeanSourceDeclaration> ParseFile(
        RepositoryFile file,
        LeanSourceFileContext context,
        LeanSourceFileContext equalityContext,
        bool? equalityAlternative,
        out ImmutableArray<string> imports,
        out ImmutableHashSet<string> customSyntax)
    {
        var tokens = LeanSourceTokenizer.Tokenize(file.Text,
            offset => equalityAlternative is { } alternative
                ? alternative && LeanSourceTokenizer.EqualityCanExposeIdentifier(file.Text, offset)
                : equalityContext.EqualityAt(offset));
        imports = ParseFileImports(file);
        var commands = context.Commands.SelectMany(TopCommands).ToImmutableArray();
        var slices = commands.Select(command => (Command: command,
            Start: IndexAt(command.Start), End: IndexAt(command.End))).Where(slice => slice.Start < slice.End)
            .ToImmutableArray();
        var starts = slices.Select(slice => slice.Start).ToImmutableArray();
        customSyntax = LeanCustomSyntaxCatalog.ParseLiterals(tokens, starts, includeLocal: false);
        var ambient = ImmutableArray.CreateBuilder<LeanSourceToken>();
        foreach (var slice in slices)
        {
            if (FindDeclarationKind(tokens, slice.Start, slice.End) < 0
                && tokens[slice.Start].Text is not ("@" or "example"))
                ambient.AddRange(tokens[slice.Start..slice.End]);
        }
        // Header material remains part of the semantic source relation.
        ambient.InsertRange(0, tokens.Where(token => token.ByteOffset < context.HeaderEnd));
        var result = ImmutableArray.CreateBuilder<LeanSourceDeclaration>();
        foreach (var slice in slices)
        {
            var start = slice.Start;
            var end = slice.End;
            var kindIndex = FindDeclarationKind(tokens, start, end);
            if (kindIndex < 0) continue;
            var kind = tokens[kindIndex].Text;
            var nameIndex = NextIdentifier(tokens, kindIndex + 1, end);
            if (nameIndex < 0) continue;
            var name = tokens[nameIndex].Identifier;
            var ns = slice.Command.Namespace;
            if (ns is "[anonymous]" or "_anonymous") ns = string.Empty;
            var fullName = name.StartsWith("_root_.", StringComparison.Ordinal) ? name[7..]
                : ns.Length == 0 ? name : ns + "." + name;
            var semanticEnd = ProofKinds.Contains(kind) ? FindProofStart(tokens, nameIndex + 1, end) : end;
            if (semanticEnd < 0)
                throw new LeanSourceExtractionException($"Lean proof boundary is unresolved for {fullName}.",
                    tokens[kindIndex].Line);
            result.Add(new(file.Path, fullName, kind, ProofKinds.Contains(kind),
                tokens[kindIndex..semanticEnd], ambient.ToImmutable(), imports, customSyntax));
        }
        return result.ToImmutable();

        int IndexAt(int offset)
        {
            var index = 0;
            while (index < tokens.Length && tokens[index].ByteOffset < offset) index++;
            return index;
        }
    }

    private static IEnumerable<LeanSourceCommand> TopCommands(LeanSourceCommand command)
    {
        if (command.Kind is "Lean.Parser.Command.in" or "Lean.Parser.Command.mutual"
            && !command.Children.IsEmpty)
        {
            var previous = command.Start;
            foreach (var child in command.Children)
            {
                // Retain wrapper syntax between commands (including `in`) as
                // ambient source material, as well as the prefix and suffix.
                if (previous < child.Start)
                    yield return command with { Start = previous, End = child.Start, Children = [] };
                foreach (var nested in TopCommands(child)) yield return nested;
                previous = child.End;
            }
            if (previous < command.End)
                yield return command with { Start = previous, Children = [] };
        }
        else yield return command;
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

        for (var index = start + 1; index < end; index++)
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
            if (tokens[index].IsIdentifier)
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

    internal static IEnumerable<string> QualifiedIdentifiers(
        ImmutableArray<LeanSourceToken> tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            // Escaped keywords are names; classify the spelling before normalization.
            if (tokens[index].IsIdentifier && !ReservedIdentifiers.Contains(tokens[index].Text))
            {
                yield return tokens[index].Identifier;
            }
        }
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
        LeanSourceTokenizer.IdentifierParts(fullName);

    private static string ModuleName(RepoPath path) =>
        path.Value[..^".lean".Length].Replace('/', '.');

    private static string NamespaceName(string fullName)
    {
        var parts = FullNameSegments(fullName);
        return LeanSourceTokenizer.IdentifierText(parts.Take(Math.Max(0, parts.Length - 1)));
    }

    private static string LeafName(string fullName)
    {
        return LeanSourceTokenizer.IdentifierText(FullNameSegments(fullName).TakeLast(1));
    }

    private static void AppendTokens(
        StringBuilder output,
        ImmutableArray<LeanSourceToken> tokens) =>
        AppendField(output, "tokens", string.Join('\u001f', tokens.Select(static token => token.Text)));

    private static void AppendField(StringBuilder output, string name, string value) =>
        output.Append(name.Length).Append(':').Append(name)
            .Append(value.Length).Append(':').Append(value).Append('\n');
}
