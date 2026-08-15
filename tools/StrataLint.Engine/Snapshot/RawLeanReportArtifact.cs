using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class RawLeanReportArtifact
{
    internal const string Schema = "stratalint-raw-lean-report-v1";
    internal const string DefaultRelativePath = ".lake/build/stratalint/raw-lean-report.json";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static LeanAxiomReport ReadFile(string path, RepositorySnapshot snapshot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        return Read(File.ReadAllBytes(path), snapshot);
    }

    internal static LeanAxiomReport Read(ReadOnlySpan<byte> bytes, RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var text = StrictUtf8.GetString(bytes);
        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("Raw Lean report is not valid JSON.", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            var mismatch = FirstMismatch(canonical.AsSpan(), bytes);
            throw new FormatException(
                "Raw Lean report bytes are not canonical JSON at byte "
                + $"{mismatch}: expected {ByteAt(canonical.AsSpan(), mismatch)}, "
                + $"actual {ByteAt(bytes, mismatch)}.");
        }

        using var document = JsonDocument.Parse(text);
        var root = document.RootElement;
        RequireProperties(root, ["modules", "schema"], "raw Lean report");
        if (RequiredString(root, "schema") != Schema)
        {
            throw new FormatException($"Raw Lean report schema must be {Schema}.");
        }

        var expected = ExpectedModules(snapshot);
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        string? previousModule = null;
        foreach (var moduleElement in RequiredArray(root, "modules").EnumerateArray())
        {
            RequireProperties(
                moduleElement,
                ["declarations", "imports", "module", "source_path", "source_sha256"],
                "raw Lean module");
            var module = RequiredString(moduleElement, "module");
            RequireStrictOrder(previousModule, module, "modules");
            previousModule = module;
            var sourcePath = RequiredString(moduleElement, "source_path");
            if (!expected.TryGetValue(module, out var source))
            {
                throw new FormatException($"Raw Lean report contains unknown module {module}.");
            }

            if (!string.Equals(source.Path.Value, sourcePath, StringComparison.Ordinal))
            {
                throw new FormatException($"Raw Lean report maps {module} to unexpected path {sourcePath}.");
            }

            var sourceSha256 = RequiredString(moduleElement, "source_sha256");
            var expectedSourceSha256 = Sha256(source.File.RawBytes.AsSpan());
            if (!string.Equals(sourceSha256, expectedSourceSha256, StringComparison.Ordinal))
            {
                throw new FormatException($"Raw Lean report source hash does not match {sourcePath}.");
            }

            var imports = ReadSortedStrings(RequiredArray(moduleElement, "imports"), "imports");
            var declarations = ReadDeclarations(RequiredArray(moduleElement, "declarations"));
            if (!reports.TryAdd(sourcePath, new LeanFileReport(imports, declarations)))
            {
                throw new FormatException($"Raw Lean report contains duplicate path {sourcePath}.");
            }
        }

        var missing = expected.Values
            .Select(static item => item.Path.Value)
            .Where(path => !reports.ContainsKey(path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (missing.Length > 0)
        {
            throw new FormatException(
                "Raw Lean report is missing modules: " + string.Join(", ", missing));
        }

        return LeanAxiomReport.Create(reports);
    }

    internal static ImmutableArray<byte> Write(RepositorySnapshot snapshot, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        var expected = ExpectedModules(snapshot);
        var material = JsonSerializer.SerializeToElement(new
        {
            modules = expected
                .OrderBy(static item => item.Key, StringComparer.Ordinal)
                .Select(item =>
                {
                    if (!report.Files.TryGetValue(item.Value.Path, out var fileReport))
                    {
                        throw new FormatException(
                            $"Lean report is missing {item.Value.Path.Value}.");
                    }

                    return new
                    {
                        declarations = fileReport.Declarations
                            .OrderBy(static declaration => declaration.NameKey, StringComparer.Ordinal)
                            .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal)
                            .ThenBy(static declaration => declaration.Name, StringComparer.Ordinal)
                            .Select(static declaration => new
                            {
                                axioms = declaration.Axioms
                                    .Distinct(StringComparer.Ordinal)
                                    .Order(StringComparer.Ordinal),
                                include_in_statement = declaration.IncludeInStatement,
                                kind = declaration.Kind,
                                name = declaration.Name,
                                name_key = declaration.NameKey,
                                type = declaration.TypeRepresentation,
                            }),
                        imports = fileReport.Imports
                            .Distinct(StringComparer.Ordinal)
                            .Order(StringComparer.Ordinal),
                        module = item.Key,
                        source_path = item.Value.Path.Value,
                        source_sha256 = Sha256(item.Value.File.RawBytes.AsSpan()),
                    };
                }),
            schema = Schema,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    internal static string ContentAddress(ReadOnlySpan<byte> canonicalBytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(canonicalBytes));

    internal static string DefaultPath(string repositoryRoot) => Path.Combine(
        Path.GetFullPath(repositoryRoot),
        DefaultRelativePath.Replace('/', Path.DirectorySeparatorChar));

    private static ImmutableArray<LeanDeclaration> ReadDeclarations(JsonElement declarations)
    {
        var builder = ImmutableArray.CreateBuilder<LeanDeclaration>();
        string? previousNameKey = null;
        foreach (var declarationElement in declarations.EnumerateArray())
        {
            RequireProperties(
                declarationElement,
                ["axioms", "include_in_statement", "kind", "name", "name_key", "type"],
                "raw Lean declaration");
            var nameKey = RequiredString(declarationElement, "name_key");
            RequireStrictOrder(previousNameKey, nameKey, "declarations");
            previousNameKey = nameKey;
            builder.Add(new LeanDeclaration(
                RequiredString(declarationElement, "name"),
                RequiredString(declarationElement, "kind"),
                RequiredString(declarationElement, "type"),
                ReadSortedStrings(RequiredArray(declarationElement, "axioms"), "axioms"))
            {
                IncludeInStatement = RequiredBoolean(declarationElement, "include_in_statement"),
                NameKey = nameKey,
            });
        }

        return builder.ToImmutable();
    }

    private static ImmutableArray<string> ReadSortedStrings(JsonElement array, string context)
    {
        var builder = ImmutableArray.CreateBuilder<string>();
        string? previous = null;
        foreach (var element in array.EnumerateArray())
        {
            if (element.ValueKind != JsonValueKind.String || element.GetString() is not { } value)
            {
                throw new FormatException($"Raw Lean report {context} must contain strings.");
            }

            RequireStrictOrder(previous, value, context);
            previous = value;
            builder.Add(value);
        }

        return builder.ToImmutable();
    }

    private static void RequireStrictOrder(string? previous, string current, string context)
    {
        if (previous is not null && string.CompareOrdinal(previous, current) >= 0)
        {
            throw new FormatException($"Raw Lean report {context} must be sorted and unique.");
        }
    }

    private static int FirstMismatch(ReadOnlySpan<byte> expected, ReadOnlySpan<byte> actual)
    {
        var shared = Math.Min(expected.Length, actual.Length);
        for (var index = 0; index < shared; index++)
        {
            if (expected[index] != actual[index]) return index;
        }

        return shared;
    }

    private static string ByteAt(ReadOnlySpan<byte> bytes, int index) =>
        index < bytes.Length ? $"0x{bytes[index]:x2}" : "end-of-file";

    private static Dictionary<string, (RepoPath Path, RepositoryFile File)> ExpectedModules(
        RepositorySnapshot snapshot) => snapshot.Files
        .Where(static item => LeanClosureValidator.IsManagedLean(item.Key.Value))
        .ToDictionary(
            static item => ModuleName(item.Key.Value),
            static item => (item.Key, item.Value),
            StringComparer.Ordinal);

    private static string ModuleName(string path) => path == "Trureturing.lean"
        ? "Trureturing"
        : path[..^5].Replace('/', '.');

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static JsonElement RequiredArray(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.Array
            ? child
            : throw new FormatException($"Raw Lean report field {property} must be an array.");

    private static string RequiredString(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.String
            ? child.GetString() ?? throw new FormatException($"Raw Lean report field {property} is null.")
            : throw new FormatException($"Raw Lean report field {property} must be a string.");

    private static bool RequiredBoolean(JsonElement element, string property) =>
        element.TryGetProperty(property, out var child)
            && child.ValueKind is JsonValueKind.True or JsonValueKind.False
                ? child.GetBoolean()
                : throw new FormatException($"Raw Lean report field {property} must be a boolean.");

    private static void RequireProperties(
        JsonElement element,
        IReadOnlyCollection<string> expected,
        string context)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{context} must be an object.");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || !actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
        {
            throw new FormatException($"{context} has unexpected fields.");
        }
    }
}
