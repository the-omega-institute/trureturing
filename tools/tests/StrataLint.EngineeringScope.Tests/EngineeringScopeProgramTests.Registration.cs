using System.Text.Json;
using System.Security.Cryptography;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class EngineeringScopeProgramTests
{
    private const string EngineeringManifestPath = "Meta/EngineeringInputs.json";

    private static void RegisterProject(string root, string path, bool test, string[] references)
    {
        var fullPath = Path.Combine(root, EngineeringManifestPath);
        var manifest = TemporaryFileSystem.File.Exists(fullPath)
            ? JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(fullPath))!.AsObject()
            : new JsonObject { ["schema_version"] = 1, ["projects"] = new JsonArray(), ["inputs"] = new JsonArray() };
        var projects = manifest["projects"]!.AsArray();
        projects.Add(JsonSerializer.SerializeToNode(new
        {
            path, assembly = Path.GetFileNameWithoutExtension(path), role = test ? "test" : "support",
            references, inputs = new[] { Path.GetDirectoryName(path)!.Replace('\\', '/') + "/**" },
        }));
        WriteFile(root, EngineeringManifestPath, manifest.ToJsonString());
    }

    private static void RegisterExtraInput(string root, string pattern, params string[] projects)
    {
        var path = Path.Combine(root, EngineeringManifestPath);
        var manifest = JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!;
        manifest["extra_inputs"] = new JsonArray(JsonSerializer.SerializeToNode(new { patterns = new[] { pattern }, projects }));
        WriteFile(root, EngineeringManifestPath, manifest.ToJsonString());
    }

    private static void CompleteRegistration(string root)
    {
        var manifest = JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(Path.Combine(root, EngineeringManifestPath)))!.AsObject();
        var projects = manifest["projects"]!.AsArray();
        var removed = projects.Where(project => !TemporaryFileSystem.File.Exists(Path.Combine(root, project!["path"]!.GetValue<string>())))
            .ToArray();
        foreach (var project in removed) projects.Remove(project);
        foreach (var project in projects)
            project!["sha256"] = Convert.ToHexStringLower(SHA256.HashData(
                TemporaryFileSystem.File.ReadAllBytes(Path.Combine(root, project["path"]!.GetValue<string>()))));
        // Synthetic fixture declarations, deliberately independent of project XML.
        var inputs = new JsonArray();
        if (manifest["extra_inputs"] is JsonArray extras)
            foreach (var extra in extras) inputs.Add(extra!.DeepClone());
        manifest.Remove("extra_inputs");
        foreach (var project in projects)
            inputs.Add(JsonSerializer.SerializeToNode(new
            {
                patterns = project!["inputs"]!.Deserialize<string[]>(),
                projects = new[] { project["path"]!.GetValue<string>() },
            }));
        foreach (var project in removed)
            inputs.Add(JsonSerializer.SerializeToNode(new { patterns = project!["inputs"]!.Deserialize<string[]>(), projects = Array.Empty<string>() }));
        inputs.Add(JsonSerializer.SerializeToNode(new
        {
            patterns = new[] { "Meta/**", "Directory.*", "tools/scripts/**", "notes/**" },
            projects = Array.Empty<string>(),
        }));
        manifest["inputs"] = inputs;
        WriteFile(root, EngineeringManifestPath, manifest.ToJsonString());
        var fileMapPath = Path.Combine(root, FileMapPath);
        if (!TemporaryFileSystem.File.Exists(fileMapPath)) return;
        var fileMap = TemporaryFileSystem.File.ReadAllText(fileMapPath);
        if (!fileMap.Contains("artifact_id = \"EngineeringInputManifest\"", StringComparison.Ordinal))
            WriteFile(root, FileMapPath, fileMap + "\n[[files]]\npattern = \"Meta/EngineeringInputs.json\"\nadmission_plane = \"judge\"\nkind = \"program\"\nartifact_id = \"EngineeringInputManifest\"\nconsumed_by = [\"EngineeringInputManifest\"]\nverified_by = [\"EngineeringInputManifest\"]\nruntime_disposition = \"committed-source\"\n");
    }
}
