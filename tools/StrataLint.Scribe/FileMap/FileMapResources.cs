using System.Collections.Immutable;
using StrataLint.Engine;
using Tomlyn.Model;

namespace StrataLint.Scribe;

internal sealed record FileMapResource(string Id, string Stage, string Owner,
    ImmutableArray<string> Prerequisites, ImmutableArray<string> Tools,
    ImmutableArray<string> CacheLayers, ImmutableArray<string> Materials);

internal static partial class FileMapLoader
{
    private static readonly string[] ResourceStages = ["build", "engineering", "current", "delta"];
    private static readonly string[] ResourceTools = ["bash", "dotnet", "git", "lake", "make", "python3"];
    private static readonly string[] ResourceCaches = ["dependency", "project", "report", "judge", "elan"];

    private static ImmutableArray<FileMapResource> ParseResources(TomlTable root, string location)
    {
        var tables = root["resources"] switch
        {
            TomlTableArray array => array.Cast<TomlTable>(),
            TomlArray array when array.All(static item => item is TomlTable) => array.Cast<TomlTable>(),
            _ => throw Invalid(location, "resources must be an array of tables"),
        };
        var resources = tables.Select(table =>
        {
            RequireExactKeys(table, location, "id", "stage", "owner", "prerequisites", "tools", "cache_layers", "materials");
            var id = RequiredName(table, "id", location, allowNone: false);
            var stage = RequiredString(table, "stage", id);
            if (!ResourceStages.Contains(stage, StringComparer.Ordinal)) throw Invalid(id, "invalid resource stage");
            var tools = RequiredNames(table, "tools", id, allowEmpty: true);
            var caches = RequiredNames(table, "cache_layers", id, allowEmpty: true);
            if (tools.Except(ResourceTools, StringComparer.Ordinal).Any()
                || caches.Except(ResourceCaches, StringComparer.Ordinal).Any())
                throw Invalid(id, "unknown resource tool/cache");
            if (table["materials"] is not TomlArray rawMaterials) throw Invalid(id, "materials must be an array");
            var materials = rawMaterials.Select(item => item is string path
                ? ResourcePath(path, id) : throw Invalid(id, "material must be a path")).ToImmutableArray();
            if (!materials.SequenceEqual(materials.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)))
                throw Invalid(id, "materials must be unique and ordinally sorted");
            return new FileMapResource(id, stage, ResourcePath(RequiredString(table, "owner", id), id),
                RequiredNames(table, "prerequisites", id, allowEmpty: true), tools, caches, materials);
        }).ToImmutableArray();
        var ids = resources.Select(static resource => resource.Id).ToArray();
        if (!ids.SequenceEqual(ids.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)))
            throw Invalid(location, "resource ids must be unique and ordinally sorted");
        var byId = resources.ToDictionary(static resource => resource.Id, StringComparer.Ordinal);
        foreach (var resource in resources)
            foreach (var dependency in resource.Prerequisites)
            {
                if (!byId.TryGetValue(dependency, out var target)) throw Invalid(resource.Id, $"unknown resource {dependency}");
                if (Array.IndexOf(ResourceStages, target.Stage) > Array.IndexOf(ResourceStages, resource.Stage))
                    throw Invalid(resource.Id, $"conflicting resource stage dependency {dependency}");
            }
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        void Visit(string id)
        {
            if (visiting.Contains(id)) throw Invalid(id, "cyclic resource");
            if (!visited.Add(id)) return;
            visiting.Add(id);
            foreach (var dependency in byId[id].Prerequisites) Visit(dependency);
            visiting.Remove(id);
        }
        foreach (var id in ids) Visit(id);
        return resources;
    }

    private static string ResourcePath(string value, string location)
    {
        if (!RepoPath.TryCreate(value, out _))
            throw Invalid(location, $"invalid resource path {value}");
        try { _ = StrictUtf8.GetByteCount(value); }
        catch (System.Text.EncoderFallbackException exception) { throw Invalid(location, "invalid UTF-8 resource path", exception); }
        return value;
    }

    private static void ValidateResourceFiles(FileMapManifest manifest, string root)
    {
        foreach (var resource in manifest.Resources)
            foreach (var path in resource.Materials.Prepend(resource.Owner))
            {
                var full = Path.Combine(root, path);
                if (!File.Exists(full) || new FileInfo(full).LinkTarget is not null || manifest.Match(path).Length != 1)
                    throw Invalid(resource.Id, $"owner/material must be a registered regular file: {path}");
            }
    }
}
