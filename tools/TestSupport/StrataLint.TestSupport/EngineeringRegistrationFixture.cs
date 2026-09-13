using System.Text.Json;

namespace StrataLint.TestSupport;

// Synthetic registration data shared by native behavior tests. No project metadata is read.
public sealed record EngineeringOwnerFixture(string Path, string Assembly);

public sealed record EngineeringProjectFixture(
    string Path,
    string Assembly,
    string Role,
    bool Ci,
    string[] Include,
    string[]? Exclude = null,
    string[]? References = null,
    EngineeringOwnerFixture? Owner = null,
    string? OwnedTestAssembly = null,
    string? TestPartition = null,
    string[]? BuildInputs = null,
    string[]? ExecutionInputs = null,
    string[]? ExecutionExcludes = null,
    string[]? ExecutionEnvironment = null,
    string RootNamespace = "Fixture",
    string[]? NamespaceExclude = null,
    string[]? GlobalNamespaceExceptions = null);

public static class EngineeringRegistrationFixture
{
    public const string Path = "Meta/engineering-projects.json";

    public static string Append(string manifest, params EngineeringProjectFixture[] projects)
    {
        var existing = System.Text.Json.Nodes.JsonNode.Parse(manifest)!;
        var added = System.Text.Json.Nodes.JsonNode.Parse(Manifest(projects))!;
        foreach (var project in added["projects"]!.AsArray())
            existing["projects"]!.AsArray().Add(project!.DeepClone());
        return existing.ToJsonString();
    }

    public static string Manifest(params EngineeringProjectFixture[] projects) => JsonSerializer.Serialize(new
    {
        version = 1,
        rule_build_inputs = Array.Empty<string>(),
        projects = projects.Select(project => new
        {
            path = project.Path,
            assembly = project.Assembly,
            role = project.Role,
            ci = project.Ci,
            include = project.Include,
            exclude = project.Exclude ?? [],
            root_namespace = project.RootNamespace,
            namespace_exclude = project.NamespaceExclude ?? [],
            global_namespace_exceptions = project.GlobalNamespaceExceptions ?? [],
            references = project.References ?? [],
            build_inputs = project.BuildInputs ?? [],
            execution_inputs = project.Role is "owned-test" or "cross-cutting-test" ? project.ExecutionInputs ?? [] : (string[]?)null,
            execution_excludes = project.Role is "owned-test" or "cross-cutting-test" ? project.ExecutionExcludes ?? [] : (string[]?)null,
            execution_environment = project.Role is "owned-test" or "cross-cutting-test" ? project.ExecutionEnvironment ?? [] : (string[]?)null,
            owner = project.Owner is null ? null : new { path = project.Owner.Path, assembly = project.Owner.Assembly },
            owned_test_assembly = project.OwnedTestAssembly,
            test_partition = project.Role is "owned-test" or "cross-cutting-test"
                ? project.TestPartition ?? System.IO.Path.GetDirectoryName(project.Path)?.Replace('\\', '/') ?? "." : null,
        }),
        historical_projects = Array.Empty<object>(),
    });
}
