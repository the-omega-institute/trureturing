using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engineering;

internal static class EngineeringProjectSchema
{
    internal const string ManifestPath = "Meta/engineering-projects.json";
    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
        RespectRequiredConstructorParameters = true,
    };

    // Identity and wire schema only. Source and topology admission belongs to Engine.
    internal static EngineeringProjectManifest Parse(string text)
    {
        try
        {
            var manifest = JsonSerializer.Deserialize<EngineeringProjectManifest>(text, Options);
            if (manifest is null || manifest.Version != 1 || manifest.Projects is null || manifest.HistoricalProjects is null)
                throw new InvalidDataException("invalid engineering project registration version or projects");
            ValidateInputPaths(manifest.RuleBuildInputs, "rule_build_inputs");
            ValidateDeclarations(manifest.Projects.Concat(manifest.HistoricalProjects));
            return manifest;
        }
        catch (JsonException exception)
        {
            throw new InvalidDataException($"invalid engineering project registration: {exception.Message}", exception);
        }
    }

    private sealed record BaseDeclarations(int Version, EngineeringProjectDeclaration[] Projects);

    private static readonly JsonSerializerOptions BaseOptions = new(Options)
    {
        // Base data consumes only declarations; every consumed field remains required.
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Skip,
    };

    internal static EngineeringProjectDeclaration[] ParseBase(string text)
    {
        try
        {
            var manifest = JsonSerializer.Deserialize<BaseDeclarations>(text, BaseOptions);
            if (manifest is null || manifest.Version != 1 || manifest.Projects is null)
                throw new InvalidDataException("invalid base engineering declaration version or projects");
            ValidateDeclarations(manifest.Projects);
            return manifest.Projects;
        }
        catch (JsonException exception)
        {
            throw new InvalidDataException($"invalid base engineering declaration: {exception.Message}", exception);
        }
    }

    internal static void ValidateInputPaths(string[] paths, string registration)
    {
        if (paths is null || paths.Distinct(StringComparer.Ordinal).Count() != paths.Length
            || paths.Any(path => path is null || !RepositoryPathSyntax.IsValid(path) || path != path.Trim()
                || path.Any(character => character is ':' or '*' or '?' || character < 32 || character > 126)))
            throw new InvalidDataException($"invalid or duplicate input registration: {registration}");
    }

    internal static void ValidateDeclarations(IEnumerable<EngineeringProjectDeclaration> projects)
    {
        var paths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var project in projects)
        {
            if (project is null || !IsProjectPath(project.Path) || !paths.Add(project.Path))
                throw new InvalidDataException($"invalid or duplicate engineering project registration: {project?.Path}");
            if (!IsAssembly(project.Assembly) || project.Role is not
                ("production" or "owned-test" or "cross-cutting-test" or "test-support" or "compile-fail-proof"))
                throw new InvalidDataException($"invalid engineering identity or role: {project.Path}");
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

    private static bool IsAssembly(string? assembly) => !string.IsNullOrWhiteSpace(assembly)
        && assembly == assembly.Trim() && !assembly.Any(character => character is '/' or '\\' or ':' || char.IsControl(character));

    private static bool IsProjectPath(string? path) => path is not null && RepositoryPathSyntax.IsValid(path)
        && path.EndsWith(".csproj", StringComparison.Ordinal) && !path.Contains(':') && !path.Contains('*');
}
