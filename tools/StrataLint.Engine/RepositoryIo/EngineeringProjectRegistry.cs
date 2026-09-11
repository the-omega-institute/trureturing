using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal sealed record EngineeringSource(string Path, string Content);

internal sealed record EngineeringProjectOwner(string Path, string Assembly);

// Data needed by topology and the base execution floor. Policy owned by other
// consumers (Compile, namespace, execution reuse) is deliberately absent.
internal record EngineeringProjectDeclaration(
    string Path,
    string Assembly,
    string Role,
    bool Ci,
    string[] References,
    EngineeringProjectOwner? Owner,
    string? OwnedTestAssembly,
    string? TestPartition)
{
    internal bool IsTest => Role is "owned-test" or "cross-cutting-test";
}

internal sealed record EngineeringProjectRegistration(
    string Path,
    string Assembly,
    string Role,
    bool Ci,
    string[] Include,
    string[] Exclude,
    string[] References,
    EngineeringProjectOwner? Owner,
    string? OwnedTestAssembly,
    string? TestPartition,
    string RootNamespace,
    string[] NamespaceExclude,
    string[] GlobalNamespaceExceptions,
    [property: JsonRequired] string[]? BuildInputs = null,
    [property: JsonRequired] string[]? ExecutionInputs = null,
    [property: JsonRequired] string[]? ExecutionExcludes = null,
    [property: JsonRequired] string[]? ExecutionEnvironment = null)
    : EngineeringProjectDeclaration(Path, Assembly, Role, Ci, References, Owner, OwnedTestAssembly, TestPartition);

internal sealed record EngineeringProjectManifest(
    int Version,
    EngineeringProjectRegistration[] Projects,
    EngineeringProjectRegistration[] HistoricalProjects,
    string[] RuleBuildInputs);

// Registration is the authority. Project/source enumeration only checks coverage and expands
// declared globs; no XML, SDK, source semantics or naming convention creates a registration.
internal sealed class EngineeringProjectRegistry
{
    internal const string ManifestPath = "Meta/engineering-projects.json";
    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
        RespectRequiredConstructorParameters = true,
    };

    private EngineeringProjectRegistry(IReadOnlyList<EngineeringProjectRegistration> projects) => Projects = projects;

    internal IReadOnlyList<EngineeringProjectRegistration> Projects { get; }

    internal static EngineeringProjectRegistry Read(RepositorySnapshot snapshot) => Read(
        snapshot.Files.Values.Select(file => new EngineeringSource(file.Path.Value, file.Text)).ToArray());

    internal static EngineeringProjectRegistry Read(IReadOnlyList<EngineeringSource> files)
    {
        var manifest = files.SingleOrDefault(file => file.Path == ManifestPath)
            ?? throw new InvalidDataException($"missing engineering project registration: {ManifestPath}");
        var registration = Parse(manifest.Content);
        var registry = new EngineeringProjectRegistry(Bind(registration.Projects, files.Select(file => file.Path), requireAll: true));
        _ = registry.ProjectInputs(registry.Projects.Select(project => project.Path), files.Select(file => file.Path), []);
        return registry;
    }

    // A base predating this manifest is still data. Candidate declarations (including explicitly
    // registered historical projects) address those bytes; no old reader or discovery runs.
    internal static IReadOnlyList<EngineeringProjectDeclaration> ReadBase(RepositorySnapshot baseline, RepositorySnapshot candidate)
    {
        if (baseline.TryGetFile(ManifestPath, out var historical))
        {
            try
            {
                var manifest = JsonSerializer.Deserialize<BaseDeclarations>(historical.Text, BaseOptions);
                if (manifest is null || manifest.Version != 1 || manifest.Projects is null)
                    throw new InvalidDataException("invalid base engineering declaration version or projects");
                ValidateDeclarations(manifest.Projects);
                return Bind(manifest.Projects, baseline.Files.Keys.Select(path => path.Value), requireAll: true);
            }
            catch (JsonException exception)
            {
                throw new InvalidDataException($"invalid base engineering declaration: {exception.Message}", exception);
            }
        }
        if (!candidate.TryGetFile(ManifestPath, out var file))
            throw new InvalidDataException($"missing engineering project registration: {ManifestPath}");
        var registration = Parse(file.Text);
        return Bind(registration.Projects.Concat(registration.HistoricalProjects).ToArray(),
            baseline.Files.Keys.Select(path => path.Value), requireAll: false);
    }

    private sealed record BaseDeclarations(int Version, EngineeringProjectDeclaration[] Projects);

    private static readonly JsonSerializerOptions BaseOptions = new(Options)
    {
        // This is a purpose-specific data projection, not the candidate schema.
        // Every consumed constructor field is still required, including nullable fields.
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Skip,
    };

    internal static IReadOnlySet<string> ReadRuleBuildInputs(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(ManifestPath, out var file))
            throw new InvalidDataException($"missing engineering project registration: {ManifestPath}");
        var inputs = Parse(file.Text).RuleBuildInputs;
        foreach (var input in inputs)
            if (!snapshot.TryGetFile(input, out _))
                throw new InvalidDataException($"registered rule build input is absent: {input} (registration {ManifestPath})");
        return inputs.Append(ManifestPath).ToHashSet(StringComparer.Ordinal);
    }

    internal static void ValidateInputPaths(string[] paths, string registration)
    {
        if (paths is null || paths.Distinct(StringComparer.Ordinal).Count() != paths.Length
            || paths.Any(path => path is null || !RepoPath.TryCreate(path, out _) || path != path.Trim()
                || path.Any(character => character is ':' or '*' or '?' || character < 32 || character > 126)))
            throw new InvalidDataException($"invalid or duplicate input registration: {registration}");
    }

    private static EngineeringProjectManifest Parse(string text)
    {
        try
        {
            var manifest = JsonSerializer.Deserialize<EngineeringProjectManifest>(text, Options);
            if (manifest is null || manifest.Version != 1 || manifest.Projects is null || manifest.HistoricalProjects is null)
                throw new InvalidDataException("invalid engineering project registration version or projects");
            ValidateInputPaths(manifest.RuleBuildInputs, "rule_build_inputs");
            ValidateDeclarations(manifest.Projects.Concat(manifest.HistoricalProjects));
            foreach (var project in manifest.Projects.Concat(manifest.HistoricalProjects))
            {
                ValidatePatterns(project.Include, project.Path);
                ValidatePatterns(project.Exclude, project.Path);
                ValidateMaterials(project.BuildInputs, [], project.Path);
                if (project.IsTest)
                {
                    ValidateMaterials(project.ExecutionInputs, project.ExecutionExcludes, project.Path);
                    if (project.ExecutionEnvironment is null || project.ExecutionEnvironment.Any(name =>
                            string.IsNullOrWhiteSpace(name) || !name.All(character => char.IsAsciiLetterOrDigit(character) || character == '_'))
                        || project.ExecutionEnvironment.Distinct(StringComparer.Ordinal).Count() != project.ExecutionEnvironment.Length)
                        throw new InvalidDataException($"missing or invalid registered execution environment: {project.Path}");
                }
                else if (project.ExecutionInputs is not null || project.ExecutionExcludes is not null || project.ExecutionEnvironment is not null)
                    throw new InvalidDataException($"execution inputs require a test role: {project.Path}");
                if (project.References is null || project.References.Any(path => !IsProjectPath(path))
                    || project.References.Distinct(StringComparer.Ordinal).Count() != project.References.Length)
                    throw new InvalidDataException($"invalid or duplicate registered project reference: {project.Path}");
                if (!IsRootNamespace(project.RootNamespace))
                    throw new InvalidDataException($"invalid registered root_namespace: {project.Path}: {project.RootNamespace}");
                ValidatePatterns(project.NamespaceExclude, project.Path);
                ValidatePatterns(project.GlobalNamespaceExceptions, project.Path);
                if (project.GlobalNamespaceExceptions.Any(path => path.Contains('*')))
                    throw new InvalidDataException($"registered global namespace exceptions must be exact source paths: {project.Path}");
            }
            return manifest;
        }
        catch (Exception exception) when (exception is JsonException or FileMapPatternException)
        {
            throw new InvalidDataException($"invalid engineering project registration: {exception.Message}", exception);
        }
    }

    private static void ValidateDeclarations(IEnumerable<EngineeringProjectDeclaration> projects)
    {
        var paths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var project in projects)
        {
            if (project is null || !IsProjectPath(project.Path) || !paths.Add(project.Path))
                throw new InvalidDataException($"invalid or duplicate engineering project registration: {project?.Path}");
            if (!IsAssembly(project.Assembly) || project.Role is not
                ("production" or "owned-test" or "cross-cutting-test" or "test-support" or "compile-fail-proof"))
                throw new InvalidDataException($"invalid engineering identity or role: {project.Path}");
            if (project.Ci && !project.IsTest)
                throw new InvalidDataException($"CI execution requires a registered test role: {project.Path}");
            if (project.Role == "production" ? !IsAssembly(project.OwnedTestAssembly) : project.OwnedTestAssembly is not null)
                throw new InvalidDataException($"invalid registered owned test identity: {project.Path}");
            if (project.Role == "owned-test"
                ? project.Owner is null || !IsProjectPath(project.Owner.Path) || !IsAssembly(project.Owner.Assembly)
                : project.Owner is not null)
                throw new InvalidDataException($"invalid registered production owner: {project.Path}");
            if (project.IsTest ? string.IsNullOrWhiteSpace(project.TestPartition)
                || project.TestPartition != project.TestPartition.Trim() : project.TestPartition is not null)
                throw new InvalidDataException($"invalid registered test partition: {project.Path}");
            if (project.References is null || project.References.Any(path => !IsProjectPath(path))
                || project.References.Distinct(StringComparer.Ordinal).Count() != project.References.Length)
                throw new InvalidDataException($"invalid or duplicate registered project reference: {project.Path}");
        }
    }

    private static IReadOnlyList<T> Bind<T>(T[] declarations,
        IEnumerable<string> filePaths, bool requireAll) where T : EngineeringProjectDeclaration
    {
        var paths = filePaths.Where(path => path.EndsWith(".csproj", StringComparison.Ordinal)).ToHashSet(StringComparer.Ordinal);
        var registered = declarations.Select(project => project.Path).ToHashSet(StringComparer.Ordinal);
        var missing = paths.Except(registered).Order(StringComparer.Ordinal).FirstOrDefault();
        if (missing is not null) throw new InvalidDataException($"unregistered engineering project: {missing}");
        if (requireAll && registered.Except(paths).Order(StringComparer.Ordinal).FirstOrDefault() is { } absent)
            throw new InvalidDataException($"registered engineering project is absent: {absent}");
        var projects = declarations.Where(project => paths.Contains(project.Path))
            .OrderBy(project => project.Path, StringComparer.Ordinal).ToArray();
        if (projects.Where(project => project.IsTest).GroupBy(project => project.TestPartition, StringComparer.Ordinal)
            .Any(group => group.Count() != 1))
            throw new InvalidDataException("duplicate registered test partition");
        return projects;
    }

    internal IReadOnlyDictionary<string, IReadOnlyList<EngineeringSource>> Sources(IReadOnlyList<EngineeringSource> files)
    {
        var sources = files.Where(file => file.Path.EndsWith(".cs", StringComparison.Ordinal))
            .OrderBy(file => file.Path, StringComparer.Ordinal).ToArray();
        var byPath = sources.ToDictionary(file => file.Path, StringComparer.Ordinal);
        var covered = new HashSet<string>(StringComparer.Ordinal);
        var result = new Dictionary<string, IReadOnlyList<EngineeringSource>>(StringComparer.Ordinal);
        foreach (var project in Projects)
        {
            var includes = project.Include.Select(FileMapGlob.Create).ToArray();
            var excludes = project.Exclude.Select(FileMapGlob.Create).ToArray();
            foreach (var pattern in project.Include.Where(pattern => !pattern.Contains('*')))
                if (!byPath.ContainsKey(pattern))
                    throw new InvalidDataException($"registered Compile input is absent from candidate source: {project.Path}: {pattern}");
            var members = sources.Where(source => includes.Any(pattern => pattern.IsMatch(source.Path))
                && !excludes.Any(pattern => pattern.IsMatch(source.Path))).ToArray();
            covered.UnionWith(members.Select(source => source.Path));
            covered.UnionWith(sources.Where(source => excludes.Any(pattern => pattern.IsMatch(source.Path))).Select(source => source.Path));
            result.Add(project.Path, members);
        }
        var unregistered = sources.FirstOrDefault(source => !covered.Contains(source.Path));
        if (unregistered is not null) throw new InvalidDataException($"unregistered engineering source: {unregistered.Path}");
        return result;
    }

    internal static string[] ExpandInputs(IEnumerable<string> paths, string[] includes, string[] excludes, string project)
    {
        var available = paths.ToHashSet(StringComparer.Ordinal);
        var include = includes.Select(FileMapGlob.Create).ToArray();
        var exclude = excludes.Select(FileMapGlob.Create).ToArray();
        foreach (var path in includes.Where(pattern => !pattern.Contains('*')))
            if (!available.Contains(path)) throw new InvalidDataException($"registered input is absent: {project}: {path}");
        return available.Where(path => include.Any(pattern => pattern.IsMatch(path))
            && !exclude.Any(pattern => pattern.IsMatch(path))).Order(StringComparer.Ordinal).ToArray();
    }

    private static void ValidateMaterials(string[]? includes, string[]? excludes, string project)
    {
        foreach (var patterns in new[] { includes, excludes })
        {
            if (patterns is null || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
                throw new InvalidDataException($"missing or duplicate registered execution/build inputs: {project}");
            foreach (var pattern in patterns)
            {
                if (pattern is null || pattern.Contains(':'))
                    throw new InvalidDataException($"invalid registered input: {project}: {pattern}");
                _ = FileMapGlob.Create(pattern);
            }
        }
        foreach (var path in includes!.Where(pattern => !pattern.Contains('*')))
            if (excludes!.Any(pattern => FileMapGlob.Create(pattern).IsMatch(path)))
                throw new InvalidDataException($"conflicting required registered input and exclusion: {project}: {path}");
    }

    internal IReadOnlySet<string> ProjectInputs(IEnumerable<string> selectedProjects,
        IEnumerable<string> currentPaths, IEnumerable<string> changedPaths)
    {
        var byPath = Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var selected = new HashSet<string>(StringComparer.Ordinal);
        var active = new HashSet<string>(StringComparer.Ordinal);
        void Visit(string path)
        {
            if (!byPath.TryGetValue(path, out var project))
                throw new InvalidDataException($"unregistered producer project reference: {path} (registration {ManifestPath})");
            if (!active.Add(path))
                throw new InvalidDataException($"cyclic producer project registration: {path}");
            if (selected.Add(path))
                foreach (var reference in project.References) Visit(reference);
            active.Remove(path);
        }
        foreach (var project in selectedProjects) Visit(project);
        if (selected.GroupBy(path => byPath[path].Assembly, StringComparer.Ordinal).Any(group => group.Count() != 1))
            throw new InvalidDataException($"conflicting selected producer assembly registration: {ManifestPath}");
        var current = currentPaths.ToHashSet(StringComparer.Ordinal);
        var paths = current.Concat(changedPaths).Distinct(StringComparer.Ordinal).ToArray();
        var inputs = new HashSet<string>(selected, StringComparer.Ordinal);
        foreach (var path in selected)
        {
            var project = byPath[path];
            foreach (var pattern in project.Include.Where(pattern => !pattern.Contains('*')))
                if (!current.Contains(pattern))
                    throw new InvalidDataException($"registered Compile input is absent: {path}: {pattern} (registration {ManifestPath})");
            var includes = project.Include.Select(FileMapGlob.Create).ToArray();
            var excludes = project.Exclude.Select(FileMapGlob.Create).ToArray();
            inputs.UnionWith(paths.Where(source => includes.Any(glob => glob.IsMatch(source))
                && !excludes.Any(glob => glob.IsMatch(source))));
        }
        return inputs;
    }

    // Namespace scope is a declared subset of Compile ownership. A linked source may have
    // multiple compile owners, but those checking it must agree on namespace and exception.
    internal IReadOnlyList<(EngineeringSource Source, string RootNamespace, bool AllowGlobalNamespace)>
        NamespaceSources(IReadOnlyList<EngineeringSource> files)
    {
        var sources = Sources(files);
        var result = new Dictionary<string, (EngineeringSource Source, EngineeringProjectRegistration Project, bool Global)>(StringComparer.Ordinal);
        foreach (var project in Projects)
        {
            var members = sources[project.Path];
            var excludes = project.NamespaceExclude.Select(FileMapGlob.Create).ToArray();
            foreach (var pattern in excludes)
                if (!members.Any(source => pattern.IsMatch(source.Path)))
                    throw new InvalidDataException($"registered namespace exclusion has no owned source: {project.Path}: {pattern.Pattern}");
            var checkedSources = members.Where(source => !excludes.Any(pattern => pattern.IsMatch(source.Path))).ToArray();
            var checkedPaths = checkedSources.Select(source => source.Path).ToHashSet(StringComparer.Ordinal);
            foreach (var path in project.GlobalNamespaceExceptions)
                if (!checkedPaths.Contains(path))
                    throw new InvalidDataException($"registered global namespace exception is not a checked source of {project.Path}: {path}");
            foreach (var source in checkedSources)
            {
                var global = project.GlobalNamespaceExceptions.Contains(source.Path, StringComparer.Ordinal);
                if (result.TryGetValue(source.Path, out var previous)
                    && (previous.Project.RootNamespace != project.RootNamespace || previous.Global != global))
                    throw new InvalidDataException($"conflicting namespace registration for {source.Path}: {previous.Project.Path} and {project.Path}");
                result[source.Path] = (source, project, global);
            }
        }
        return result.Values.OrderBy(value => value.Source.Path, StringComparer.Ordinal)
            .Select(value => (value.Source, value.Project.RootNamespace, value.Global)).ToArray();
    }

    private static void ValidatePatterns(string[] patterns, string project)
    {
        if (patterns is null || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
            throw new InvalidDataException($"missing or duplicate registered source patterns: {project}");
        foreach (var pattern in patterns)
        {
            if (pattern is null || !pattern.EndsWith(".cs", StringComparison.Ordinal) || pattern.Contains(':'))
                throw new InvalidDataException($"invalid registered source pattern: {project}: {pattern}");
            _ = FileMapGlob.Create(pattern);
        }
    }

    private static bool IsAssembly(string? assembly) => !string.IsNullOrWhiteSpace(assembly)
        && assembly == assembly.Trim() && !assembly.Any(character => character is '/' or '\\' or ':' || char.IsControl(character));

    private static bool IsRootNamespace(string? value) => value is not null && value.Split('.').All(part =>
        Microsoft.CodeAnalysis.CSharp.SyntaxFacts.IsValidIdentifier(part)
        && part.All(character => char.IsAsciiLetterOrDigit(character) || character == '_'));

    private static bool IsProjectPath(string? path) => path is not null && RepoPath.TryCreate(path, out _)
        && path.EndsWith(".csproj", StringComparison.Ordinal) && !path.Contains(':') && !path.Contains('*');
}
