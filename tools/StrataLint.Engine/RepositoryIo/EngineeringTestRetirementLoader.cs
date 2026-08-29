using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal enum EngineeringTestRetirementDisposition
{
    Unknown,
    Retired,
    Renamed,
    Moved,
}

internal sealed record EngineeringTestIdentity(string Assembly, string Id);

internal sealed record EngineeringTestRetirementDeclaration(
    int SchemaVersion,
    string Assembly,
    string Id,
    EngineeringTestRetirementDisposition Disposition,
    EngineeringTestIdentity? Replacement,
    string Reason)
{
    [JsonIgnore]
    internal string Path { get; init; } = string.Empty;
}

internal sealed class EngineeringTestIdentityComparer : IEqualityComparer<(string Assembly, string Id)>
{
    internal static readonly EngineeringTestIdentityComparer Instance = new();

    public bool Equals((string Assembly, string Id) x, (string Assembly, string Id) y) =>
        StringComparer.OrdinalIgnoreCase.Equals(x.Assembly, y.Assembly)
        && StringComparer.Ordinal.Equals(x.Id, y.Id);

    public int GetHashCode((string Assembly, string Id) value) =>
        HashCode.Combine(
            StringComparer.OrdinalIgnoreCase.GetHashCode(value.Assembly),
            StringComparer.Ordinal.GetHashCode(value.Id));
}

internal static class EngineeringTestRetirementLoader
{
    internal const string DirectoryPath = "Golden/EngineeringTestRetirements";

    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(DirectoryPath + "/", StringComparison.Ordinal)
            || !path.EndsWith(".json", StringComparison.Ordinal))
        {
            return false;
        }

        var relative = path[(DirectoryPath.Length + 1)..^".json".Length];
        return relative.Length != 0 && !relative.Contains('/', StringComparison.Ordinal);
    }

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        Converters = { new JsonStringEnumConverter(JsonNamingPolicy.SnakeCaseLower, allowIntegerValues: false) },
    };

    internal static IReadOnlyDictionary<(string Assembly, string Id), EngineeringTestRetirementDeclaration> Load(
        string repositoryRoot,
        IReadOnlyList<string> changedPaths,
        IReadOnlyList<EngineeringSelectedTest> expectedTests)
    {
        var expected = expectedTests
            .Select(static test => (test.Assembly, test.Id))
            .ToHashSet(EngineeringTestIdentityComparer.Instance);
        var result = new Dictionary<(string Assembly, string Id), EngineeringTestRetirementDeclaration>(
            EngineeringTestIdentityComparer.Instance);
        foreach (var path in changedPaths
                     .Where(IsCanonicalPath)
                     .Distinct(StringComparer.Ordinal)
                     .Order(StringComparer.Ordinal))
        {
            var fullPath = Path.Combine(repositoryRoot, path.Replace('/', Path.DirectorySeparatorChar));
            if (!File.Exists(fullPath))
            {
                continue;
            }

            var declaration = JsonSerializer.Deserialize<EngineeringTestRetirementDeclaration>(
                    File.ReadAllText(fullPath, StrictUtf8),
                    JsonOptions)
                ?? throw new InvalidDataException($"test retirement declaration is empty: {path}");
            declaration = declaration with { Path = path };
            Validate(declaration, expected);
            if (!result.TryAdd((declaration.Assembly, declaration.Id), declaration))
            {
                throw new InvalidDataException(
                    $"duplicate test retirement declaration for {declaration.Assembly}::{declaration.Id}");
            }
        }

        return result;
    }

    private static void Validate(
        EngineeringTestRetirementDeclaration declaration,
        IReadOnlySet<(string Assembly, string Id)> expected)
    {
        if (declaration.SchemaVersion != 1
            || string.IsNullOrWhiteSpace(declaration.Assembly)
            || string.IsNullOrWhiteSpace(declaration.Id)
            || string.IsNullOrWhiteSpace(declaration.Reason)
            || declaration.Disposition == EngineeringTestRetirementDisposition.Unknown)
        {
            throw new InvalidDataException(
                $"test retirement declaration does not conform to schema version 1: {declaration.Path}");
        }

        if (!expected.Contains((declaration.Assembly, declaration.Id)))
        {
            throw new InvalidDataException(
                $"test retirement declaration does not address a planned base identity: {declaration.Path}");
        }

        if (declaration.Disposition == EngineeringTestRetirementDisposition.Retired)
        {
            if (declaration.Replacement is not null)
            {
                throw new InvalidDataException(
                    $"retired test declaration must not name a replacement: {declaration.Path}");
            }

            return;
        }

        if (declaration.Replacement is not { } replacement
            || string.IsNullOrWhiteSpace(replacement.Assembly)
            || string.IsNullOrWhiteSpace(replacement.Id)
            || EngineeringTestIdentityComparer.Instance.Equals(
                (declaration.Assembly, declaration.Id),
                (replacement.Assembly, replacement.Id)))
        {
            throw new InvalidDataException(
                $"{declaration.Disposition.ToString().ToLowerInvariant()} test declaration must name a distinct replacement: {declaration.Path}");
        }
    }
}
