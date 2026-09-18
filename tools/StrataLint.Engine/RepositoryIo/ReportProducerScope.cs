using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

// The pointer names an authored scope in the sole native report input manifest.
// It carries project roots for existing consumers, never a second source inventory.
internal sealed record ReportProducerScope(string Schema, string Registration, string Scope, string[] Projects)
{
    internal const string InputManifest = "lean-report-inputs.json";
    private sealed record Include(string Pattern, bool Optional);
    private sealed record PathSet(Include[] Include, string[] Exclude);
    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
        RespectRequiredConstructorParameters = true,
    };

    internal static ReportProducerScope Read(RepositorySnapshot snapshot, string path)
    {
        try
        {
            if (!snapshot.TryGetFile(path, out var file))
                throw new InvalidDataException($"missing producer registration: {path}");
            var producer = JsonSerializer.Deserialize<ReportProducerScope>(file.Text, Options);
            if (producer is null || producer.Schema != "report-producer-scope-v2" || producer.Projects is null
                || producer.Scope is not ("lean-report" or "scribe-content") || producer.Registration != InputManifest)
                throw new InvalidDataException($"invalid producer registration: {path}");
            var inputs = producer.Projects.Append(producer.Registration).ToArray();
            EngineeringProjectRegistry.ValidateInputPaths(inputs, path);
            if (producer.Projects.Any(project => !project.EndsWith(".csproj", StringComparison.Ordinal)))
                throw new InvalidDataException($"invalid producer project registration: {path}");
            foreach (var input in inputs)
                if (!snapshot.TryGetFile(input, out _))
                    throw new InvalidDataException($"producer {path} references absent input: {input}");
            _ = ScopeElement(NativeManifest(snapshot), producer.Scope);
            return producer;
        }
        catch (JsonException exception)
        {
            throw new InvalidDataException($"invalid producer {path}: {exception.Message}", exception);
        }
    }

    internal static IReadOnlySet<string> RegisteredInputs(RepositorySnapshot snapshot, string path, RawChangeSet changes)
    {
        var producer = Read(snapshot, path);
        try
        {
            var manifest = NativeManifest(snapshot);
            var selections = new List<JsonElement> { ScopeElement(manifest, "lean-report") };
            if (producer.Scope == "scribe-content") selections.Add(ScopeElement(manifest, producer.Scope));
            if (!manifest.TryGetProperty("inspector_sources", out var inspector))
                throw new InvalidDataException($"{InputManifest}: missing inspector_sources");
            selections.Add(inspector);
            var current = snapshot.Files.Keys.Select(file => file.Value).ToArray();
            var possible = current.Concat(changes.Paths.Select(file => file.Value)).Distinct(StringComparer.Ordinal).ToArray();
            var inputs = new HashSet<string>(StringComparer.Ordinal) { path, InputManifest, EngineeringProjectRegistry.ManifestPath };
            foreach (var selection in selections)
            {
                var set = selection.Deserialize<PathSet>(Options);
                if (set?.Include is null || set.Exclude is null)
                    throw new InvalidDataException($"{InputManifest}: invalid producer path set");
                var exclude = set.Exclude.Select(FileMapGlob.Create).ToArray();
                foreach (var include in set.Include)
                {
                    if (include is null) throw new InvalidDataException($"{InputManifest}: invalid producer include");
                    var glob = FileMapGlob.Create(include.Pattern);
                    bool Matches(string source) => glob.IsMatch(source) && !exclude.Any(item => item.IsMatch(source));
                    if (!include.Optional && !current.Any(Matches))
                        throw new InvalidDataException($"{InputManifest}: required registration has no files after exclusions: {include.Pattern}");
                    inputs.UnionWith(possible.Where(Matches));
                }
            }
            var registry = EngineeringProjectRegistry.Read(snapshot);
            inputs.UnionWith(registry.ProjectInputs(producer.Projects, current, changes.Paths.Select(file => file.Value)));
            return inputs;
        }
        catch (Exception exception) when (exception is JsonException or FormatException)
        {
            throw new InvalidDataException($"invalid producer {path}: {exception.Message}", exception);
        }
    }

    private static JsonElement NativeManifest(RepositorySnapshot snapshot) =>
        JsonSerializer.Deserialize<JsonElement>(snapshot.Files[RepoPath.CreateKnown(InputManifest)].Text, Options);

    private static JsonElement ScopeElement(JsonElement manifest, string scope)
    {
        if (manifest.ValueKind != JsonValueKind.Object
            || !manifest.TryGetProperty("producer_scopes", out var scopes) || scopes.ValueKind != JsonValueKind.Object
            || !scopes.TryGetProperty(scope, out var selected) || selected.ValueKind != JsonValueKind.Object)
            throw new InvalidDataException($"{InputManifest}: absent registered scope: {scope}");
        return selected;
    }
}
