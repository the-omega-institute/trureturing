using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal static partial class FileMapLoader
{
    private static readonly Regex SelectorPattern = new("^[A-Za-z0-9_.-]+$", RegexOptions.CultureInvariant);

    private static ImmutableDictionary<ArtifactKindId, ArtifactPolicy> ParseEvidence(TomlTable root, string location)
    {
        if (root["evidence"] is not TomlTable evidence)
            throw Invalid(location, "evidence must be a table");
        RequireExactKeys(evidence, location + ":evidence", "artifact_kinds");
        if (evidence["artifact_kinds"] is not TomlTable kinds || kinds.Count == 0)
            throw Invalid(location, "evidence.artifact_kinds must be a non-empty table");
        var result = ImmutableDictionary.CreateBuilder<ArtifactKindId, ArtifactPolicy>();
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var (name, raw) in kinds)
        {
            if (!ArtifactKindId.TryCreate(name, out var id) || !names.Add(name))
                throw Invalid(location, $"invalid, duplicate, or case-colliding artifact kind: {name}");
            if (raw is not TomlTable kind) throw Invalid(location, $"artifact kind {name} must be a table");
            RequireExactKeys(kind, location + ":" + name, "profile", "selectors", "path_selectors");
            var profile = RequiredString(kind, "profile", location) switch
            {
                "structured-json" => (ValidationProfile)new ValidationProfile.StructuredJson(),
                "structured-yaml" => new ValidationProfile.StructuredYaml(),
                "opaque-text" => new ValidationProfile.OpaqueText(),
                _ => throw Invalid(location, $"unknown Evidence profile for {name}"),
            };
            result.Add(id, new ArtifactPolicy(profile,
                EvidenceSelectors(kind, "selectors", location, static value => value is not "." and not ".." && SelectorPattern.IsMatch(value)),
                EvidenceSelectors(kind, "path_selectors", location, static value => value is "experiments" or "formal" or "kernels" or "special" or "values")));
        }
        return result.ToImmutable();
    }

    private static ImmutableHashSet<string> EvidenceSelectors(TomlTable table, string key, string location, Func<string, bool> valid)
    {
        if (table[key] is not TomlArray array || array.Count == 0)
            throw Invalid(location, $"{key} must be a non-empty array");
        var result = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var raw in array)
        {
            if (raw is not string value || !valid(value) || !folded.Add(value) || !result.Add(value))
                throw Invalid(location, $"invalid, duplicate, or case-colliding {key} value: {raw}");
        }
        return result.ToImmutable();
    }
}
