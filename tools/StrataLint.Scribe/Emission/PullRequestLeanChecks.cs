using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static class PullRequestLeanChecks
{
    private const string Inspector = "tools/lean-inspector/";
    private const string Interface = "tools/lean-inspector-interface/";

    // Resolve Lake's module name independently of whether the file survived the diff.
    private static string? Module(string path)
    {
        if (LeanClosureValidator.IsReportLean(path)) return path[..^5].Replace('/', '.');
        if (!path.EndsWith(".lean", StringComparison.Ordinal) || path.EndsWith("/lakefile.lean", StringComparison.Ordinal))
            return null;
        var prefix = path.StartsWith(Inspector, StringComparison.Ordinal) ? Inspector : Interface;
        return path.StartsWith(prefix, StringComparison.Ordinal) ? path[prefix.Length..^5].Replace('/', '.') : null;
    }

    private static RepositorySnapshot Sources(string root, bool pins)
    {
        var raw = GitRepositorySnapshotReader.ReadCurrent(root, readContents: path => Module(path) is not null
            || pins && FrozenStatePath.IsUnderRoot(path) || path == ReportProducerScope.InputManifest,
            pathspecs: ["D5", "Reg", "Trureturing.lean", Inspector, Interface, "Golden/Frozen/state",
                ReportProducerScope.InputManifest, ":(glob)Meta/*"]);
        return SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded accepted => accepted.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
        };
    }

    internal static int Plan(string root, ImmutableArray<string> paths, TextWriter output)
    {
        var changed = paths.Select(Module).OfType<string>().ToHashSet(StringComparer.Ordinal);
        var targets = new HashSet<string>(StringComparer.Ordinal);
        var programs = new HashSet<string>(StringComparer.Ordinal);
        var scribePaths = paths.ToHashSet(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (FrozenStatePath.IsUnderRoot(path) && File.Exists(Path.Combine(root, path)))
            {
                if (!FrozenStatePath.TryToModulePath(path, out var owner)
                    || !File.Exists(Path.Combine(root, owner.Value)) || Module(owner.Value) is not { } module)
                    throw new InvalidDataException("invalid frozen state owner: " + path);
                targets.Add(module);
            }
            if (!path.StartsWith("Blueprint/", StringComparison.Ordinal)) continue;
            var stem = path.EndsWith(".md", StringComparison.Ordinal) ? path[..^3]
                : path.EndsWith(".scribe.cs", StringComparison.Ordinal) ? path[..^10] : null;
            if (stem is null) continue;
            if (File.Exists(Path.Combine(root, stem + ".md")) && !File.Exists(Path.Combine(root, stem + ".scribe.cs")))
                throw new InvalidDataException("Blueprint markdown has no matching .scribe.cs source: " + stem + ".md");
            scribePaths.Add(stem + ".scribe.cs");
        }
        if (changed.Count > 0)
            AddAffectedModules(Sources(root, pins: false), changed, targets, programs);
        var selected = ScribeDefinitionSelector.Select(root, scribePaths);
        if (!selected.IsSuccess) throw new InvalidDataException(selected.Failure);
        var definitions = selected.Paths.IsEmpty ? ImmutableDictionary<string, string[]>.Empty
            : ScribeLeanInputs.ByDefinition(root, selected.Paths);
        targets.UnionWith(definitions.Values.SelectMany(static roots => roots));
        output.WriteLine(JsonSerializer.Serialize(new
        {
            targets = targets.Order(StringComparer.Ordinal),
            programs = programs.Order(StringComparer.Ordinal),
            paths = scribePaths.Order(StringComparer.Ordinal),
            definitions,
        }));
        return 0;
    }

    internal static void AddAffectedModules(RepositorySnapshot snapshot, HashSet<string> changed,
        HashSet<string> targets, HashSet<string> programs)
    {
        var consumers = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var file in snapshot.Files.Values)
        {
            if (Module(file.Path.Value) is not { } name) continue;
            sources.Add(name, file.Path.Value);
            IEnumerable<string> dependencies = LeanSourceCatalog.ParseFileImports(file);
            if (RepositoryRules.TryHeader(file, out var header)
                && UtilitySyntax.TryParse(header.Utility, out var utility, out _) && utility is not null)
                dependencies = dependencies.Concat(UtilityDeclarationValidator.DeclarationReferences(utility)
                    .Select(static reference => LeanImportClosure.ModuleName(reference.Path)));
            foreach (var dependency in dependencies)
            {
                if (!consumers.TryGetValue(dependency, out var importers))
                    consumers[dependency] = importers = new(StringComparer.Ordinal);
                importers.Add(name);
            }
        }

        var pending = new Queue<string>(changed);
        while (pending.TryDequeue(out var name))
        {
            if (sources.TryGetValue(name, out var path))
            {
                if (LeanClosureValidator.IsReportLean(path)) targets.Add(name);
                else programs.Add(name);
            }
            else if (snapshot.TryGetFile(FrozenStatePath.Root + name.Replace('.', '/') + ".lean.json", out _))
                throw new InvalidDataException("frozen module is missing: " + name);
            if (consumers.TryGetValue(name, out var importers))
                foreach (var importer in importers)
                    if (changed.Add(importer)) pending.Enqueue(importer);
        }
    }

    internal static ImmutableArray<RuleFinding> ProofFindings(LeanAxiomReport report) =>
        RepositoryRules.Sorry(report).AddRange(RepositoryRules.Axioms(report));

    internal static int Check(string root, string artifact, ImmutableArray<string> targets,
        ImmutableArray<string> paths, TextWriter output, TextWriter error)
    {
        var snapshot = Sources(root, pins: true);
        var scope = LeanReportScope.Create(snapshot, targets.Select(RepoPath.CreateKnown));
        var report = RawLeanReportArtifact.ReadFileForScope(artifact, scope, validateMaterials: true);
        var lean = LeanClosureValidator.Validate(scope.SourceSnapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
        };
        var frozen = snapshot.Files.Values.Where(file => FrozenStatePath.TryToModulePath(file.Path.Value, out var owner)
            && scope.Paths.Contains(owner));
        var findings = RepositoryRules.FrozenStates(scope.SourceSnapshot, lean, frozen).AddRange(ProofFindings(report));
        foreach (var finding in findings) error.WriteLine(finding.Path + ": " + finding.Message);
        if (!findings.IsEmpty) return 1;
        var emitted = ScribeEmitter.EmitPaths(root, paths, true, output, error, report);
        return emitted != 0 ? emitted : ScribeContentChecks.Run(root, paths, report, true, output, error);
    }
}
