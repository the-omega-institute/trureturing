using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record LeanSourceDeclaration(
    RepoPath Path,
    string FullName,
    string Kind,
    bool IsProof,
    ImmutableArray<LeanSourceToken> SemanticTokens,
    ImmutableArray<LeanSourceToken> AmbientTokens,
    ImmutableArray<string> Imports,
    ImmutableHashSet<string> CustomSyntaxLiterals)
{
    internal bool IsAnonymousOnlySource { get; init; }
    internal bool HasExtIffTheorem { get; init; }
    internal bool IsPrivateDeclaration { get; init; }
    internal bool HasUnsafeOrMetaModifier { get; init; }
    internal bool IsTopLevelDeclaration { get; init; }
    internal ImmutableArray<RepositoryFile> ImportedInductionSources { get; init; }
    internal ImmutableHashSet<string> NamedGenerators { get; init; } = ImmutableHashSet<string>.Empty;
}

internal sealed record LeanSourceScope(string? NamespaceName);

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
            "constant",
            "alias");
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
    private readonly ImmutableDictionary<RepoPath, ImmutableArray<LeanSourceToken>> declarationFreeSources;
    private readonly ImmutableDictionary<string, LeanSourceDeclaration> anonymousSourcesByModule;

    private LeanSourceCatalog(
        ImmutableArray<LeanSourceDeclaration> declarations,
        ImmutableDictionary<string, ImmutableArray<string>> importsByModule,
        ImmutableDictionary<string, ImmutableHashSet<string>> customSyntaxByModule,
        ImmutableDictionary<RepoPath, ImmutableArray<LeanSourceToken>> declarationFreeSources,
        ImmutableDictionary<string, RepositoryFile> sourceModules)
    {
        this.declarations = declarations;
        this.importsByModule = importsByModule;
        this.declarationFreeSources = declarationFreeSources;
        this.sourceModules = sourceModules;
        anonymousSourcesByModule = declarations
            .GroupBy(static declaration => ModuleName(declaration.Path), StringComparer.Ordinal)
            .Select(static group => group.First())
            .Select(static source => source with
            {
                FullName = ModuleName(source.Path) + "._anonymous_instance_source",
                Kind = "instance", IsProof = false, IsAnonymousOnlySource = true,
                SemanticTokens = ImplicitInstanceCommands(source.AmbientTokens)
                    .SelectMany(static command => command).ToImmutableArray(),
            })
            .Where(static source => !source.SemanticTokens.IsEmpty)
            .ToImmutableDictionary(static source => ModuleName(source.Path), StringComparer.Ordinal);
        customSyntaxCatalog = new LeanCustomSyntaxCatalog(
            importsByModule,
            customSyntaxByModule);
        byFullName = declarations
            .Where(static declaration => !declaration.IsAnonymousOnlySource)
            .GroupBy(static declaration => declaration.FullName, StringComparer.Ordinal)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group.ToImmutableArray(),
                StringComparer.Ordinal);
        byLeafName = declarations
            .Where(static declaration => !declaration.IsAnonymousOnlySource)
            .GroupBy(static declaration => LeafName(declaration.FullName), StringComparer.Ordinal)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group.ToImmutableArray(),
                StringComparer.Ordinal);
    }

    internal static LeanSourceCatalog Parse(RepositorySnapshot snapshot)
    {
        var declarations = ImmutableArray.CreateBuilder<LeanSourceDeclaration>();
        var declarationFreeSources = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<LeanSourceToken>>();
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
            var fileDeclarations = ParseFile(file, out var imports, out var customSyntax);
            declarations.AddRange(fileDeclarations);
            if (fileDeclarations.IsEmpty)
                declarationFreeSources.Add(file.Path, LeanSourceTokenizer.Tokenize(file.Text));
            var moduleName = ModuleName(file.Path);
            importsByModule.Add(moduleName, imports);
            customSyntaxByModule.Add(moduleName, customSyntax);
        }

        return new LeanSourceCatalog(
            declarations.ToImmutable(),
            importsByModule.ToImmutable(),
            customSyntaxByModule.ToImmutable(),
            declarationFreeSources.ToImmutable(),
            snapshot.Files.Values.Where(static file => LeanClosureValidator.IsManagedLean(file.Path.Value))
                .ToImmutableDictionary(static file => ModuleName(file.Path), StringComparer.Ordinal));
    }

    internal static ImmutableArray<string> ParseFileImports(RepositoryFile file, bool includeImplicitInit = false)
    {
        ArgumentNullException.ThrowIfNull(file);

        // Imports belong to the module header, not to later commands or quotations.
        // Read lazily so arbitrary body syntax need not be tokenized to read base data.
        // Lean.Parser.Module.Syntax: [module] [prelude] ([public] [meta] import [all] ident)*.
        using var tokens = LeanSourceTokenizer.ReadTokens(file.Text, importHeader: true).GetEnumerator();
        var current = tokens.MoveNext() ? tokens.Current : null;
        Consume("module");
        var prelude = Consume("prelude");
        var imports = ImmutableArray.CreateBuilder<string>();
        if (includeImplicitInit && !prelude) imports.Add("Init");
        while (current is not null)
        {
            Consume("public");
            Consume("meta");
            if (!Consume("import")) break;
            Consume("all");
            if (current is null || !IsIdentifierStart(current.Text[0]))
                throw new LeanSourceExtractionException("Lean import requires a module identifier.");
            // Escaping a plain name segment does not change the imported module.
            // Preserve escapes containing punctuation/whitespace, which name different segments.
            imports.Add(Regex.Replace(current.Text, @"«([\p{L}\p{Nl}_][\p{L}\p{Nl}\p{Nd}\p{Mn}\p{Mc}\p{No}_']*)»", "$1",
                RegexOptions.CultureInvariant));
            current = tokens.MoveNext() ? tokens.Current : null;
        }

        return imports.Distinct(StringComparer.Ordinal).ToImmutableArray();

        bool Consume(string keyword)
        {
            if (current?.Text != keyword) return false;
            current = tokens.MoveNext() ? tokens.Current : null;
            return true;
        }
    }

    internal ImmutableArray<byte> ExtractPropositionSource(
        RepoPath modulePath,
        ImmutableArray<FrozenDeclaration> recordedDeclarations)
    {
        if (!recordedDeclarations.IsDefault && recordedDeclarations.IsEmpty
            && declarationFreeSources.TryGetValue(modulePath, out var emptyModuleTokens))
        {
            var emptyModule = new StringBuilder();
            AppendField(emptyModule, "root-kind", "declaration-free-module");
            AppendField(emptyModule, "root-name", ModuleName(modulePath));
            AppendTokens(emptyModule, emptyModuleTokens);
            return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(emptyModule.ToString()));
        }

        var moduleDeclarations = declarations
            .Where(declaration => declaration.Path == modulePath)
            .ToImmutableArray();
        if (moduleDeclarations.IsEmpty || recordedDeclarations.IsDefaultOrEmpty)
        {
            throw new LeanSourceExtractionException(
                $"Lean proposition source is unavailable for {modulePath.Value}.");
        }

        var roots = ImmutableArray.CreateBuilder<(FrozenDeclaration Recorded, LeanSourceDeclaration Source)>();
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

            if (!declaration.ImportedInductionSources.IsDefaultOrEmpty) continue;
            RejectCustomSyntaxDependency(declaration);
            foreach (var dependency in ResolveDependencies(declaration))
            {
                if (dependency.IsProof && declaration.Kind != "alias")
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
        foreach (var root in roots.Select(static root => root.Source)
            .Where(static source => !IsGeneratorClosure(source))
            .DistinctBy(static source => source.FullName, StringComparer.Ordinal)
            .OrderBy(static source => source.FullName, StringComparer.Ordinal))
        {
            if (!root.ImportedInductionSources.IsDefaultOrEmpty)
            {
                AppendImportedInductionSource(output, root);
                continue;
            }
            AppendField(output, "root-kind", root.Kind);
            AppendField(output, "root-name", root.FullName);
            AppendTokens(output, root.AmbientTokens);
            AppendTokens(output, root.SemanticTokens);
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

    private LeanSourceDeclaration ResolveRecordedDeclaration(
        ImmutableArray<LeanSourceDeclaration> moduleDeclarations,
        FrozenDeclaration recorded)
    {
        var recordedSegments = DecodeNameKey(recorded.DeclarationNameKey);
        if (recordedSegments.IsEmpty)
        {
            throw new LeanSourceExtractionException(
                $"Lean declaration name key cannot be resolved: {recorded.DeclarationNameKey}.");
        }

        var matches = moduleDeclarations
            .Where(declaration => !declaration.IsAnonymousOnlySource
                && NameKeyCanReferTo(recordedSegments, declaration.FullName))
            .OrderByDescending(static declaration => declaration.FullName.Length)
            .ToImmutableArray();
        if (matches.IsEmpty)
        {
            if (recordedSegments[^1] == "induct_unfolding"
                && !HasNamedGenerator(moduleDeclarations[0], recorded.DeclarationNameKey))
                return ResolveImportedFunctionInduction(moduleDeclarations[0], recorded, recordedSegments);

            var extParents = moduleDeclarations.Where(source => source.HasExtIffTheorem
                && source.IsPrivateDeclaration == IsPrivateNameKey(recorded.DeclarationNameKey)
                && HasSourceBoundName(source, recorded.DeclarationNameKey, [source.FullName + "_iff"]))
                .ToImmutableArray();
            if (!extParents.IsEmpty)
            {
                if (recorded.Kind != "theorem" || extParents.Length != 1)
                    throw new LeanSourceExtractionException(
                        $"Lean ext iff theorem source is inconsistent: {recorded.DeclarationNameKey}.");
                var parent = extParents[0];
                return parent with { FullName = parent.FullName + "_iff", Kind = "theorem" };
            }

            if (IsCompilerGeneratedName(recordedSegments, moduleDeclarations)
                || HasNamedGenerator(moduleDeclarations[0], recorded.DeclarationNameKey)
                || recordedSegments.Any(static segment => LeafName(segment).StartsWith("tactic", StringComparison.Ordinal))
                    && GeneratorCommands(moduleDeclarations[0].AmbientTokens).Any(static command =>
                    {
                        var header = command.TakeWhile(static token => token.Text != "=>").ToImmutableArray();
                        return header.Length >= 2 && header[^2].Text == ":" && header[^1].Text == "tactic";
                    }))
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

    private IEnumerable<LeanSourceDeclaration> ResolveDependencies(
        LeanSourceDeclaration declaration)
    {
        if (IsGeneratorClosure(declaration))
        {
            foreach (var source in declarations.Where(source => source.Path == declaration.Path))
            {
                foreach (var dependency in ResolveDependencies(source))
                {
                    yield return dependency;
                }
            }

            foreach (var command in GeneratorCommands(declaration.AmbientTokens))
            {
                foreach (var dependency in ResolveTokenDependencies(declaration, command, respectBinders: false))
                    yield return dependency;
            }

            yield break;
        }

        if (declaration.IsAnonymousOnlySource)
        {
            foreach (var command in ImplicitInstanceCommands(declaration.AmbientTokens))
                foreach (var dependency in ResolveTokenDependencies(declaration, command, respectBinders: true))
                    yield return dependency;
        }
        else
        {
            var dependencyTokens = declaration.SemanticTokens.RemoveAt(1);
            foreach (var dependency in ResolveTokenDependencies(declaration, dependencyTokens, respectBinders: true))
                yield return dependency;
        }

        foreach (var source in VisibleAnonymousSourceClosures(declaration))
            yield return source;
    }

    private IEnumerable<LeanSourceDeclaration> VisibleAnonymousSourceClosures(LeanSourceDeclaration owner)
    {
        var queue = new Queue<string>(owner.Imports.Prepend(ModuleName(owner.Path)));
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var module))
        {
            if (!visited.Add(module)) continue;
            if (anonymousSourcesByModule.TryGetValue(module, out var source)) yield return source;
            if (importsByModule.TryGetValue(module, out var imports))
                foreach (var import in imports) queue.Enqueue(import);
        }
    }

    private IEnumerable<LeanSourceDeclaration> ResolveTokenDependencies(
        LeanSourceDeclaration declaration, ImmutableArray<LeanSourceToken> tokens, bool respectBinders)
    {
        var bound = respectBinders ? BoundIdentifiers(tokens) : ImmutableHashSet<string>.Empty;
        foreach (var name in QualifiedIdentifiers(tokens)
            .Where(name => !IsBoundIdentifier(name, bound) && !ReservedIdentifiers.Contains(name))
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
                !declaration.IsAnonymousOnlySource && declaration.Path == owner.Path
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
        var operandEnd = name.Length;
        while (operandEnd > 1 && name[operandEnd - 1] is 'ˣ' or 'ᴴ')
        {
            yield return name[..--operandEnd];
        }
        for (var separator = name.LastIndexOf('.'); separator > 0;
            separator = name.LastIndexOf('.', separator - 1))
        {
            yield return name[..separator];
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
            foreach (var source in declarations.Where(source => source.Path == declaration.Path))
            {
                RejectCustomSyntaxDependency(source);
            }

            foreach (var command in GeneratorCommands(declaration.AmbientTokens))
            {
                var isRules = command.Any(static token => token.Text is "macro_rules" or "elab_rules");
                RejectCustomSyntaxTokens(declaration, isRules ? command
                    : command.SkipWhile(static token => token.Text != "=>").Skip(1));
            }

            return;
        }

        RejectCustomSyntaxTokens(declaration, declaration.SemanticTokens);
        foreach (var command in ImplicitInstanceCommands(declaration.AmbientTokens))
            RejectCustomSyntaxTokens(declaration, command);
    }

    private void RejectCustomSyntaxTokens(
        LeanSourceDeclaration declaration, IEnumerable<LeanSourceToken> tokens)
    {
        var semantic = tokens
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
        var commandDepths = CommandDelimiterDepths(tokens, commandStarts);
        RejectIndentedDeclarations(tokens, commandStarts, file.Path);
        imports = ParseFileImports(file);
        customSyntax = LeanCustomSyntaxCatalog.ParseLiterals(
            tokens,
            commandStarts,
            includeLocal: false);
        var moduleCustomSyntax = LeanCustomSyntaxCatalog.ParseLiterals(
            tokens,
            commandStarts,
            includeLocal: false);
        var ambientTokens = ParseAmbientTokens(tokens, commandStarts);
        var scopeStack = new List<LeanSourceScope>();
        var namedGenerators = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var result = ImmutableArray.CreateBuilder<LeanSourceDeclaration>();
        var pendingAttributes = ImmutableArray<LeanSourceToken>.Empty;
        for (var commandIndex = 0; commandIndex < commandStarts.Length; commandIndex++)
        {
            var start = commandStarts[commandIndex];
            var end = commandIndex + 1 < commandStarts.Length
                ? commandStarts[commandIndex + 1]
                : tokens.Length;
            var command = tokens[start].Text;
            var kindIndex = FindDeclarationKind(tokens, start, end);
            if (kindIndex < 0 && IsAttributePrefix(tokens[start..end]))
            {
                pendingAttributes = commandDepths[commandIndex] == 0
                    ? pendingAttributes.AddRange(tokens[start..end])
                    : ImmutableArray<LeanSourceToken>.Empty;
                continue;
            }
            var attributes = kindIndex >= 0
                ? pendingAttributes.AddRange(tokens[start..kindIndex])
                : ImmutableArray<LeanSourceToken>.Empty;
            pendingAttributes = ImmutableArray<LeanSourceToken>.Empty;
            if (commandDepths[commandIndex] == 0 && FindSectionHeaderEnd(tokens, start, end) >= 0)
            {
                scopeStack.Add(new LeanSourceScope(null));
                continue;
            }
            if (command == "namespace" && commandDepths[commandIndex] == 0)
            {
                var namespaceName = ReadQualifiedName(tokens, start + 1, end);
                if (namespaceName.Length == 0)
                {
                    throw new LeanSourceExtractionException(
                        $"Lean namespace is malformed in {file.Path.Value}.");
                }

                foreach (var segment in FullNameSegments(namespaceName))
                    scopeStack.Add(new LeanSourceScope(segment));
                continue;
            }

            if (commandDepths[commandIndex] == 0 && command == "mutual")
            {
                scopeStack.Add(new LeanSourceScope(null));
                continue;
            }

            if (command == "end" && commandDepths[commandIndex] == 0)
            {
                if (scopeStack.Count == 0)
                {
                    throw new LeanSourceExtractionException(
                        $"Lean scope terminator is unmatched in {file.Path.Value}.");
                }

                var endName = ReadQualifiedName(tokens, start + 1, end);
                var scopeCount = Math.Max(1, FullNameSegments(endName).Length);
                if (scopeCount > scopeStack.Count)
                    throw new LeanSourceExtractionException(
                        $"Lean scope terminator is unmatched in {file.Path.Value}.");
                scopeStack.RemoveRange(scopeStack.Count - scopeCount, scopeCount);
                continue;
            }

            if (kindIndex < 0)
            {
                var generatedName = NamedGeneratorName(tokens[start..end]);
                if (generatedName is not null)
                    namedGenerators.Add(QualifySourceName(generatedName, scopeStack));
                continue;
            }

            var kind = tokens[kindIndex].Text;
            if (kind == "alias" && !IsPlainAlias(tokens, kindIndex, end))
                throw new LeanSourceExtractionException($"Lean alias source is unsupported in {file.Path.Value}.");
            var nameIndex = kind == "instance" ? InstanceNameIndex(tokens, kindIndex, end)
                : NextIdentifier(tokens, kindIndex + 1, end);
            if (nameIndex < 0 || IsAnonymousInstance(tokens, kindIndex, end))
            {
                continue;
            }

            var name = tokens[nameIndex].Text;
            var fullName = QualifySourceName(name, scopeStack);
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
                kind == "def" && HasDeclarationModifier(attributes, "partial") ? "opaque" : kind,
                ProofKinds.Contains(kind),
                tokens[kindIndex..semanticEnd],
                ambientTokens,
                imports,
                moduleCustomSyntax)
            {
                HasExtIffTheorem = commandDepths[commandIndex] == 0
                    && ProofKinds.Contains(kind) && HasBareExtAttribute(attributes),
                IsPrivateDeclaration = HasDeclarationModifier(attributes, "private"),
                IsTopLevelDeclaration = commandDepths[commandIndex] == 0,
                HasUnsafeOrMetaModifier = HasDeclarationModifier(attributes, "unsafe")
                    || HasDeclarationModifier(attributes, "meta"),
            });
        }

        if (result.Count == 0)
        {
            var anonymousTokens = ImplicitInstanceCommands(ambientTokens)
                .SelectMany(static command => command).ToImmutableArray();
            if (!anonymousTokens.IsEmpty)
            {
                result.Add(new LeanSourceDeclaration(
                    file.Path, ModuleName(file.Path) + "._anonymous_instance_source",
                    "instance", IsProof: false, anonymousTokens, ambientTokens,
                    imports, moduleCustomSyntax) { IsAnonymousOnlySource = true });
            }
        }

        var generatedNames = namedGenerators.ToImmutable();
        return result.Select(declaration => declaration with { NamedGenerators = generatedNames })
            .ToImmutableArray();
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
            var kindIndex = FindDeclarationKind(tokens, start, end);
            if (kindIndex < 0 && tokens[start].Text is not ("@" or "example")
                || IsAnonymousInstance(tokens, kindIndex, end)
                || IsNamedInstance(tokens, kindIndex, end))
            {
                result.AddRange(tokens[start..end]);
            }
            else if (tokens[start].Text is "set_option" or "include" or "omit" or "open")
            {
                result.AddRange(tokens[start..FindDeclarationKind(tokens, start, end)]);
            }
        }

        result.AddRange(AttributedInstanceCommands(tokens).SelectMany(static command => command));
        return result.ToImmutable();
    }

    private static bool IsAnonymousInstance(
        ImmutableArray<LeanSourceToken> tokens, int kindIndex, int end) =>
        kindIndex >= 0 && tokens[kindIndex].Text == "instance"
        && InstanceNameIndex(tokens, kindIndex, end) < 0;

    private static IEnumerable<ImmutableArray<LeanSourceToken>> ImplicitInstanceCommands(
        ImmutableArray<LeanSourceToken> tokens) =>
        AnonymousInstanceCommands(tokens).Concat(AttributedInstanceCommands(tokens))
            .Concat(NamedInstanceCommands(tokens));

    private static IEnumerable<ImmutableArray<LeanSourceToken>> AttributedInstanceCommands(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var starts = FindCommandStarts(tokens);
        var pending = ImmutableArray<LeanSourceToken>.Empty;
        for (var index = 0; index < starts.Length; index++)
        {
            var start = starts[index];
            var end = index + 1 < starts.Length ? starts[index + 1] : tokens.Length;
            var kindIndex = FindDeclarationKind(tokens, start, end);
            if (kindIndex < 0 && IsAttributePrefix(tokens[start..end]))
            {
                pending = pending.AddRange(tokens[start..end]);
                continue;
            }
            var attributes = kindIndex >= 0 ? pending.AddRange(tokens[start..kindIndex])
                : ImmutableArray<LeanSourceToken>.Empty;
            pending = ImmutableArray<LeanSourceToken>.Empty;
            if (kindIndex >= 0 && !IsAnonymousInstance(tokens, kindIndex, end)
                && HasInstanceAttribute(attributes))
                yield return attributes.AddRange(tokens[kindIndex..end]);
        }
    }

    private static IEnumerable<ImmutableArray<LeanSourceToken>> AnonymousInstanceCommands(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var starts = FindCommandStarts(tokens);
        for (var index = 0; index < starts.Length; index++)
        {
            var start = starts[index];
            var end = index + 1 < starts.Length ? starts[index + 1] : tokens.Length;
            if (IsAnonymousInstance(tokens, FindDeclarationKind(tokens, start, end), end))
                yield return tokens[start..end];
        }
    }

    private static IEnumerable<ImmutableArray<LeanSourceToken>> GeneratorCommands(
        ImmutableArray<LeanSourceToken> tokens)
    {
        var starts = FindCommandStarts(tokens);
        for (var index = 0; index < starts.Length; index++)
        {
            var start = starts[index];
            var end = index + 1 < starts.Length ? starts[index + 1] : tokens.Length;
            var command = tokens[start..end];
            if (command.Any(static token =>
                token.Text is "macro" or "macro_rules" or "syntax" or "notation" or "elab" or "elab_rules"))
                yield return command;
        }
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
        IsIdentifierStart(value) || char.IsDigit(value) || value is '\'' or '.' or '?' or '!';

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
