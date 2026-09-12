using System.Collections.Immutable;
using System.Text.Json;
using System.Security.Cryptography;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal sealed record EngineeringProject(
    string Path, string Assembly, string Role, string Sha256,
    ImmutableArray<string> References, ImmutableArray<string> Inputs);

// FILEMAP registers the manifest; the manifest declares membership, input ownership
// and impact edges. Git enumerates material only to verify/consume those declarations.
internal sealed class EngineeringInputManifest
{
    internal const string Identity = "EngineeringInputManifest";
    internal ImmutableArray<EngineeringProject> Projects { get; }
    private readonly ImmutableArray<Input> inputs;
    private readonly ImmutableArray<string> comparisonProjects;

    private EngineeringInputManifest(ImmutableArray<EngineeringProject> projects, ImmutableArray<Input> inputs,
        ImmutableArray<string> comparisonProjects)
    {
        Projects = projects;
        this.inputs = inputs;
        this.comparisonProjects = comparisonProjects;
    }

    internal static EngineeringInputManifest ReadCurrent(string repository)
    {
        var files = GitIndexRepositoryFiles.Enumerate(repository).ToDictionary(file => file.RelativePath, StringComparer.Ordinal);
        return Load(path => files.TryGetValue(path, out var file)
            ? File.ReadAllText(file.FullPath) : throw Invalid(path, "missing tracked manifest material"), files.Values.Select(file => file.RelativePath), path => File.ReadAllBytes(files[path].FullPath));
    }

    internal static EngineeringInputManifest Read(RepositorySnapshot snapshot) =>
        Load(path => snapshot.Files.Values.FirstOrDefault(file => file.Path.Value == path) is { } file
            ? file.Text : throw Invalid(path, "missing manifest material"), snapshot.Files.Keys.Select(path => path.Value),
            path => snapshot.Files.Values.First(file => file.Path.Value == path).RawBytes.ToArray());

    internal EngineeringInputManifest ReadComparison(RepositorySnapshot snapshot)
    {
        var fileMap = snapshot.Files.Values.FirstOrDefault(file => file.Path.Value == AdmissionPlanePolicy.FileMapPath)
            ?? throw Invalid(AdmissionPlanePolicy.FileMapPath, "missing comparison classification declarations");
        var table = TomlSerializer.Deserialize<TomlTable>(fileMap.Text)
            ?? throw Invalid(AdmissionPlanePolicy.FileMapPath, "invalid comparison FILEMAP");
        var entries = Field(table, "files") as TomlTableArray
            ?? throw Invalid(AdmissionPlanePolicy.FileMapPath, "missing comparison files registrations");
        if (entries.Any(entry => Equals(Field(entry, "artifact_id"), Identity))) return Read(snapshot);
        // The first installation declares exactly which pre-manifest project bytes
        // may be compared. Current declarations alone do not authorize a baseline.
        foreach (var path in snapshot.Files.Keys.Select(path => path.Value)
            .Where(path => path.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase)))
            if (!comparisonProjects.Contains(path))
                throw Invalid(path, "missing pre-manifest comparison project registration");
        return new(Projects.Where(project => comparisonProjects.Contains(project.Path)).ToImmutableArray(),
            inputs, comparisonProjects);
    }

    private static EngineeringInputManifest Load(Func<string, string> read, IEnumerable<string> paths, Func<string, byte[]> readBytes)
    {
        var fileMap = TomlSerializer.Deserialize<TomlTable>(read(AdmissionPlanePolicy.FileMapPath))
            ?? throw Invalid(AdmissionPlanePolicy.FileMapPath, "invalid FILEMAP");
        var entries = Field(fileMap, "files") as TomlTableArray
            ?? throw Invalid(AdmissionPlanePolicy.FileMapPath, "missing files registrations");
        var registered = entries.Where(entry => entry.TryGetValue("artifact_id", out var id) && Equals(id, Identity)).ToArray();
        if (registered.Length != 1) throw Invalid(Identity, "requires exactly one FILEMAP registration");
        var registration = registered[0];
        var path = Field(registration, "pattern") as string ?? throw Invalid(Identity, "missing manifest path");
        _ = FileMapGlob.Create(path);
        if (path.Contains('*') || !Equals(Field(registration, "kind"), "program")
            || !Equals(Field(registration, "admission_plane"), "judge")
            || !Equals(Field(registration, "runtime_disposition"), "committed-source")
            || Field(registration, "consumed_by") is not TomlArray consumers || !consumers.Contains(Identity)
            || Field(registration, "verified_by") is not TomlArray verifiers || !verifiers.Contains(Identity))
            throw Invalid(path, "conflicting FILEMAP manifest registration");
        var result = Parse(read(path), path);
        var present = paths.ToHashSet(StringComparer.Ordinal);
        foreach (var project in result.Projects)
        {
            if (!present.Contains(project.Path)) throw Invalid(project.Path, "registered project material is missing");
            VerifyProjectMaterial(project, readBytes(project.Path));
            foreach (var pattern in project.Inputs)
            {
                var matches = present.Where(FileMapGlob.Create(pattern).IsMatch).ToArray();
                if (matches.Length == 0)
                    throw Invalid(pattern, $"registered compiler inputs for {project.Path} match no material");
                foreach (var material in matches)
                    if (!result.Owners(material).Contains(project.Path))
                        throw Invalid(material, $"compiler input has no declared impact on {project.Path}");
            }
        }
        result.ValidateProjectCoverage(present);
        return result;
    }

    // This rejects undeclared objects; it never adds a project or an impact edge.
    internal void ValidateProjectCoverage(IEnumerable<string> paths)
    {
        foreach (var path in paths.Where(path => path.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase)))
            if (!Projects.Any(project => project.Path == path))
                throw Invalid(path, "missing project registration");
    }

    internal static void VerifyProjectMaterial(EngineeringProject project, ReadOnlySpan<byte> content)
    {
        if (Convert.ToHexStringLower(SHA256.HashData(content)) != project.Sha256)
            throw Invalid(project.Path, "registered project sha256 differs from material");
    }

    private static object? Field(TomlTable table, string name) =>
        table.TryGetValue(name, out var value) ? value : null;

    internal static EngineeringInputManifest Parse(string text, string location)
    {
        try { return ParseDeclarations(text, location); }
        catch (Exception exception) when (exception is JsonException or InvalidOperationException or KeyNotFoundException or FormatException)
        {
            throw Invalid(location, "invalid declaration: " + exception.Message);
        }
    }

    private static EngineeringInputManifest ParseDeclarations(string text, string location)
    {
        using var document = JsonDocument.Parse(text);
        var root = document.RootElement;
        Keys(root, location, root.TryGetProperty("comparison_projects", out var comparison)
            ? ["schema_version", "projects", "inputs", "comparison_projects"]
            : ["schema_version", "projects", "inputs"]);
        if (root.GetProperty("schema_version").GetInt32() != 1) throw Invalid(location, "schema_version must be 1");
        var projects = ImmutableArray.CreateBuilder<EngineeringProject>();
        foreach (var item in root.GetProperty("projects").EnumerateArray())
        {
            Keys(item, location, "path", "assembly", "role", "references", "inputs", "sha256");
            var path = Text(item.GetProperty("path"), location);
            if (!RepoPath.TryCreate(path, out _) || path.Contains('*') || !path.EndsWith(".csproj", StringComparison.Ordinal)) throw Invalid(path, "invalid project path");
            var role = Text(item.GetProperty("role"), path);
            if (role is not ("production" or "test" or "harness" or "support" or "negative-control"))
                throw Invalid(path, "invalid project role " + role);
            var assembly = Text(item.GetProperty("assembly"), path);
            var sha256 = Text(item.GetProperty("sha256"), path);
            if (sha256.Length != 64 || sha256.Any(character => !char.IsAsciiHexDigitLower(character)))
                throw Invalid(path, "sha256 must be a complete lowercase digest");
            var projectInputs = Strings(item.GetProperty("inputs"), path);
            if (projectInputs.IsEmpty) throw Invalid(path, "missing compiler input declarations");
            foreach (var pattern in projectInputs) _ = FileMapGlob.Create(pattern);
            if (projects.Any(project => project.Path == path || string.Equals(project.Assembly, assembly, StringComparison.OrdinalIgnoreCase)))
                throw Invalid(path, "conflicting project/assembly registrations: " + assembly);
            projects.Add(new(path, assembly, role, sha256, Strings(item.GetProperty("references"), path), projectInputs));
        }
        var known = projects.Select(project => project.Path).ToHashSet(StringComparer.Ordinal);
        var comparisonProjects = comparison.ValueKind == JsonValueKind.Undefined
            ? ImmutableArray<string>.Empty : Strings(comparison, location);
        foreach (var project in comparisonProjects)
            if (!known.Contains(project)) throw Invalid(project, "missing comparison project declaration");
        foreach (var project in projects)
            foreach (var reference in project.References)
                if (!known.Contains(reference)) throw Invalid(reference, "missing impact project registration required by " + project.Path);
        var inputs = ImmutableArray.CreateBuilder<Input>();
        foreach (var item in root.GetProperty("inputs").EnumerateArray())
        {
            Keys(item, location, "patterns", "projects");
            var patterns = Strings(item.GetProperty("patterns"), location);
            if (patterns.IsEmpty) throw Invalid(location, "input patterns must not be empty");
            var owners = Strings(item.GetProperty("projects"), location);
            foreach (var owner in owners)
                if (!known.Contains(owner)) throw Invalid(owner, "missing input owner registration");
            inputs.Add(new(patterns.Select(FileMapGlob.Create).ToImmutableArray(), owners));
        }
        return new(projects.ToImmutable(), inputs.ToImmutable(), comparisonProjects);
    }

    internal ImmutableArray<string> Owners(string path)
    {
        var matches = inputs.Where(input => input.Patterns.Any(pattern => pattern.IsMatch(path))).ToArray();
        if (matches.Length == 0) throw Invalid(path, "missing input registration");
        if (matches.Length > 1) throw Invalid(path, "conflicting input registrations");
        return matches.SelectMany(input => input.Projects).ToImmutableArray();
    }

    internal static bool IsTest(EngineeringProject project) => project.Role is "test" or "harness";

    private static ImmutableArray<string> Strings(JsonElement value, string location)
    {
        var values = value.EnumerateArray().Select(item => Text(item, location)).ToImmutableArray();
        if (values.Distinct(StringComparer.Ordinal).Count() != values.Length) throw Invalid(location, "duplicate declaration");
        return values;
    }

    private static string Text(JsonElement value, string location) =>
        value.ValueKind == JsonValueKind.String && value.GetString() is { Length: > 0 } text
            ? text : throw Invalid(location, "expected nonempty string");

    private static void Keys(JsonElement value, string location, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object
            || !value.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal)
                .SequenceEqual(expected.Order(StringComparer.Ordinal)))
            throw Invalid(location, "missing, duplicate or unknown declaration fields");
    }

    private static InvalidDataException Invalid(string path, string defect) =>
        new($"ENGINEERING-REGISTRATION {path}: {defect}");

    private sealed record Input(ImmutableArray<FileMapGlob> Patterns, ImmutableArray<string> Projects);
}
