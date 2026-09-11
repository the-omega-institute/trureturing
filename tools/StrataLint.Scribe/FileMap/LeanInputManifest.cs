using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

// Input selection is declaration consumption. Neither compiler evaluation nor
// script/source analysis supplies ownership or augments a declared scope.
internal static class LeanInputManifest
{
    private const string Identity = "LeanInputManifest";

    internal static IReadOnlyDictionary<string, string[]> Select(string repository, string[] requested)
    {
        var fileMap = FileMapLoader.LoadRepository(repository);
        var registrations = fileMap.Entries.Where(entry => entry.ArtifactId == Identity).ToArray();
        if (registrations.Length != 1)
            throw Invalid(Identity, "requires exactly one FILEMAP registration");
        var registration = registrations[0];
        if (registration.Kind != FileMapKind.Program || registration.AdmissionPlane != FileMapAdmissionPlane.Judge
            || registration.Pattern.Contains('*') || registration.RuntimeDisposition != "committed-source"
            || !registration.ConsumedBy.Contains(Identity) || !registration.VerifiedBy.Contains(Identity))
            throw Invalid(registration.Pattern, "conflicting FILEMAP registration for " + Identity);
        var manifestPath = Path.Combine(repository, registration.Pattern);
        using var document = JsonDocument.Parse(File.ReadAllBytes(manifestPath));
        var root = document.RootElement;
        Keys(root, registration.Pattern, "schema_version", "scopes");
        if (root.GetProperty("schema_version").GetInt32() != 1)
            throw Invalid(registration.Pattern, "schema_version must be 1");
        var scopes = new Dictionary<string, JsonElement>(StringComparer.Ordinal);
        foreach (var scope in root.GetProperty("scopes").EnumerateArray())
        {
            Keys(scope, registration.Pattern, "name", "includes", "inputs");
            var name = Text(scope.GetProperty("name"), registration.Pattern);
            if (!scopes.TryAdd(name, scope)) throw Invalid(name, "conflicting scope registrations");
        }
        var result = new Dictionary<string, string[]>(StringComparer.Ordinal);
        foreach (var name in requested)
        {
            var paths = new List<string>();
            var owners = new Dictionary<string, string>(StringComparer.Ordinal);
            var visiting = new HashSet<string>(StringComparer.Ordinal);
            var expanded = new HashSet<string>(StringComparer.Ordinal);
            Expand(name);
            result.Add(name, paths.ToArray());

            void Expand(string current)
            {
                if (!scopes.TryGetValue(current, out var scope)) throw Invalid(current, "missing scope registration");
                if (!visiting.Add(current)) throw Invalid(current, "cyclic scope registration");
                if (expanded.Add(current))
                {
                    foreach (var included in Strings(scope.GetProperty("includes"), current)) Expand(included);
                    var index = 0;
                    foreach (var input in scope.GetProperty("inputs").EnumerateArray())
                    {
                        var owner = $"{current}.inputs[{index++}]";
                        Keys(input, owner, "patterns", "exclude", "optional_root", "min_matches");
                        var patterns = Strings(input.GetProperty("patterns"), owner);
                        if (patterns.Length == 0) throw Invalid(owner, "patterns must not be empty");
                        var excludes = Strings(input.GetProperty("exclude"), owner).Select(FileMapGlob.Create).ToArray();
                        var minimum = input.GetProperty("min_matches").GetInt32();
                        if (minimum < 0) throw Invalid(owner, "min_matches must be nonnegative");
                        var optional = input.GetProperty("optional_root");
                        if (optional.ValueKind != JsonValueKind.Null)
                        {
                            var directory = Text(optional, owner);
                            _ = FileMapGlob.Create(directory);
                            if (directory.Contains('*') || patterns.Any(pattern => !pattern.StartsWith(directory + "/", StringComparison.Ordinal)))
                                throw Invalid(owner, "optional_root must contain all declared patterns");
                            if (File.Exists(Path.Combine(repository, directory))) throw Invalid(directory, "optional library is not a directory");
                            if (!Directory.Exists(Path.Combine(repository, directory))) continue;
                        }
                        var matches = patterns.SelectMany(pattern => ExpandPattern(repository, pattern))
                            .Where(path => !excludes.Any(exclude => exclude.IsMatch(path))).ToArray();
                        if (matches.Length < minimum)
                            throw Invalid(string.Join(", ", patterns), $"{owner} requires at least {minimum} input(s), found {matches.Length}");
                        foreach (var path in matches)
                        {
                            if (!owners.TryAdd(path, owner)) throw Invalid(path, $"conflicting input registrations: {owners[path]} and {owner}");
                            paths.Add(path);
                        }
                    }
                }
                visiting.Remove(current);
            }
        }
        return result;
    }

    private static IEnumerable<string> ExpandPattern(string repository, string pattern)
    {
        var glob = FileMapGlob.Create(pattern);
        var wildcard = pattern.IndexOf('*');
        if (wildcard < 0)
            return File.Exists(Path.Combine(repository, pattern)) ? [pattern] : [];
        var slash = pattern.LastIndexOf('/', wildcard);
        var prefix = slash < 0 ? "" : pattern[..slash];
        var directory = Path.Combine(repository, prefix);
        if (!Directory.Exists(directory)) return [];
        return Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(repository, path).Replace('\\', '/'))
            .Where(glob.IsMatch).Order(StringComparer.Ordinal);
    }

    private static string Text(JsonElement value, string location) =>
        value.ValueKind == JsonValueKind.String && value.GetString() is { Length: > 0 } text
            ? text : throw Invalid(location, "expected nonempty string");

    private static string[] Strings(JsonElement value, string location)
    {
        var strings = value.EnumerateArray().Select(item => Text(item, location)).ToArray();
        if (strings.Distinct(StringComparer.Ordinal).Count() != strings.Length)
            throw Invalid(location, "conflicting duplicate entries");
        return strings;
    }

    private static void Keys(JsonElement value, string location, params string[] keys)
    {
        var actual = value.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal);
        if (!actual.SequenceEqual(keys.Order(StringComparer.Ordinal)))
            throw Invalid(location, "missing, duplicate or unknown declaration fields");
    }

    private static FormatException Invalid(string location, string defect) =>
        new($"{Identity}: {location}: {defect}");
}
