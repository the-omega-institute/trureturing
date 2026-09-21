using StrataLint.Engine;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record RegisteredFileMapRelatedScope(string[] Inputs, string[] Paths, string? Trigger = null);
internal sealed record RegisteredFileMapScope(string[] WholeTreeInputs, string[] ActorInputs, RegisteredFileMapRelatedScope[] Related,
    string[]? InventoryInputs = null);

// The planner has already validated the complete endpoint list. Expansion uses
// only registered patterns; it never discovers consumers from file contents.
internal sealed record FileMapInspectionScope(string[]? Paths, bool Actors, string[]? RelatedPatterns = null, bool Inventory = false)
{
    internal static FileMapInspectionScope Read(string path)
    {
        var result = JsonSerializer.Deserialize<FileMapInspectionScope>(File.ReadAllText(path), new JsonSerializerOptions
        {
            PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
            UnmappedMemberHandling = System.Text.Json.Serialization.JsonUnmappedMemberHandling.Disallow,
            RespectRequiredConstructorParameters = true, AllowDuplicateProperties = false,
        }) ?? throw new InvalidDataException("missing filemap inspection scope");
        if (result.Paths is null && !result.Actors || result.Paths is { } paths
            && (paths.Any(path => !RepoPath.TryCreate(path, out _)) || !paths.SequenceEqual(paths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal))))
            throw new InvalidDataException("invalid filemap inspection scope");
        if (result.RelatedPatterns is { } related)
        {
            if (!related.SequenceEqual(related.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)))
                throw new InvalidDataException("invalid filemap related scope");
            foreach (var pattern in related) _ = FileMapGlob.Create(pattern);
        }
        return result;
    }

    internal static FileMapInspectionScope Select(RegisteredFileMapScope? registration,
        IReadOnlyCollection<string>? changes, IReadOnlyCollection<string> inventory)
    {
        if (changes is null) return new(null, true);
        if (registration is null) throw new InvalidDataException("missing filemap delta scope registration");
        Validate(registration);
        if (Matches(registration.WholeTreeInputs, changes)) return new(null, true);
        var selected = changes.ToHashSet(StringComparer.Ordinal);
        // The validated endpoint list retains deletions and old rename paths;
        // those alone are absent from the candidate's complete path inventory.
        var currentPaths = inventory.ToHashSet(StringComparer.Ordinal);
        var removed = changes.Where(path => !currentPaths.Contains(path)).ToArray();
        var relatedPatterns = registration.Related.Where(row => Matches(row.Inputs, row.Trigger == "removed" ? removed : changes))
            .SelectMany(row => row.Paths).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        if (relatedPatterns.Length != 0)
        {
            var patterns = relatedPatterns.Select(FileMapGlob.Create).ToArray();
            foreach (var path in inventory.Where(path => patterns.Any(pattern => pattern.IsMatch(path)))) selected.Add(path);
        }
        return new(selected.Order(StringComparer.Ordinal).ToArray(), Matches(registration.ActorInputs, changes), relatedPatterns,
            Matches(registration.InventoryInputs!, changes));
    }

    internal static void Validate(RegisteredFileMapScope registration)
    {
        if (registration.WholeTreeInputs is null || registration.ActorInputs is null || registration.InventoryInputs is null || registration.Related is null
            || registration.Related.Any(row => row is null || row.Inputs is null || row.Paths is null))
            throw new InvalidDataException("invalid filemap delta scope registration");
        if (registration.Related.Any(row => row.Trigger is not ("changed" or "removed")))
            throw new InvalidDataException("invalid filemap related trigger: expected changed or removed");
        foreach (var patterns in new[] { registration.WholeTreeInputs, registration.ActorInputs, registration.InventoryInputs }
            .Concat(registration.Related.SelectMany(row => new[] { row.Inputs, row.Paths })))
        {
            if (patterns.Length == 0 || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
                throw new InvalidDataException("empty or duplicate filemap delta scope patterns");
            foreach (var pattern in patterns) _ = FileMapGlob.Create(pattern);
        }
    }

    private static bool Matches(string[] patterns, IEnumerable<string> paths) =>
        patterns.Select(FileMapGlob.Create).Any(pattern => paths.Any(pattern.IsMatch));
}
