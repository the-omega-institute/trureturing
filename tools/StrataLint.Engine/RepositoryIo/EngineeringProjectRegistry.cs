using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal sealed record EngineeringProjectOwner(string Path, string Assembly);

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
    string? TestPartition)
{
    internal bool IsTest => Role is "owned-test" or "cross-cutting-test";
}

internal sealed record EngineeringProjectManifest(
    int Version,
    EngineeringProjectRegistration[] Projects,
    EngineeringProjectRegistration[] HistoricalProjects);

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
        snapshot.Files.Values.Select(file => new ScribeTrackedSource(file.Path.Value, file.Text)).ToArray());

    internal static EngineeringProjectRegistry Read(IReadOnlyList<ScribeTrackedSource> files)
    {
        var manifest = files.SingleOrDefault(file => file.Path == ManifestPath)
            ?? throw new InvalidDataException($"missing engineering project registration: {ManifestPath}");
        var registration = Parse(manifest.Content);
        return Bind(registration.Projects, files.Select(file => file.Path), requireAll: true);
    }

    // A base predating this manifest is still data. Candidate declarations (including explicitly
    // registered historical projects) address those bytes; no old reader or discovery runs.
    internal static EngineeringProjectRegistry ReadBase(RepositorySnapshot baseline, RepositorySnapshot candidate)
    {
        if (baseline.TryGetFile(ManifestPath, out _)) return Read(baseline);
        if (!candidate.TryGetFile(ManifestPath, out var file))
            throw new InvalidDataException($"missing engineering project registration: {ManifestPath}");
        var manifest = Parse(file.Text);
        return Bind(manifest.Projects.Concat(manifest.HistoricalProjects).ToArray(),
            baseline.Files.Keys.Select(path => path.Value), requireAll: false);
    }

    internal static RepositorySnapshot AddressBase(RepositorySnapshot baseline, RepositorySnapshot candidate)
    {
        if (baseline.TryGetFile(ManifestPath, out _)) return baseline;
        var registrations = ReadBase(baseline, candidate);
        var text = JsonSerializer.Serialize(new EngineeringProjectManifest(1, registrations.Projects.ToArray(), []), Options);
        var raw = RawRepositoryEntry.FromText(ManifestPath, text);
        return RepositorySnapshot.Create(baseline.Files.Add(RepoPath.CreateKnown(ManifestPath),
            new RepositoryFile(RepoPath.CreateKnown(ManifestPath), raw.Bytes, text)));
    }

    private static EngineeringProjectManifest Parse(string text)
    {
        try
        {
            var manifest = JsonSerializer.Deserialize<EngineeringProjectManifest>(text, Options);
            if (manifest is null || manifest.Version != 1 || manifest.Projects is null || manifest.HistoricalProjects is null)
                throw new InvalidDataException("invalid engineering project registration version or projects");
            var paths = new HashSet<string>(StringComparer.Ordinal);
            foreach (var project in manifest.Projects.Concat(manifest.HistoricalProjects))
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
                ValidatePatterns(project.Include, project.Path);
                ValidatePatterns(project.Exclude, project.Path);
                if (project.References is null || project.References.Any(path => !IsProjectPath(path))
                    || project.References.Distinct(StringComparer.Ordinal).Count() != project.References.Length)
                    throw new InvalidDataException($"invalid or duplicate registered project reference: {project.Path}");
            }
            return manifest;
        }
        catch (Exception exception) when (exception is JsonException or FileMapPatternException)
        {
            throw new InvalidDataException($"invalid engineering project registration: {exception.Message}", exception);
        }
    }

    private static EngineeringProjectRegistry Bind(EngineeringProjectRegistration[] declarations,
        IEnumerable<string> filePaths, bool requireAll)
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
        return new EngineeringProjectRegistry(projects);
    }

    internal IReadOnlyDictionary<string, IReadOnlyList<ScribeTrackedSource>> Sources(IReadOnlyList<ScribeTrackedSource> files)
    {
        var sources = files.Where(file => file.Path.EndsWith(".cs", StringComparison.Ordinal))
            .OrderBy(file => file.Path, StringComparer.Ordinal).ToArray();
        var byPath = sources.ToDictionary(file => file.Path, StringComparer.Ordinal);
        var covered = new HashSet<string>(StringComparer.Ordinal);
        var result = new Dictionary<string, IReadOnlyList<ScribeTrackedSource>>(StringComparer.Ordinal);
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

    private static bool IsProjectPath(string? path) => path is not null && RepoPath.TryCreate(path, out _)
        && path.EndsWith(".csproj", StringComparison.Ordinal) && !path.Contains(':') && !path.Contains('*');
}
