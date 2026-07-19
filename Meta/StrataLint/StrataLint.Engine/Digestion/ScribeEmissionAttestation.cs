using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record ScribeEmissionRecord(
    string Gid,
    string DefinitionPath,
    string DefinitionSha256,
    string EmissionPath,
    string EmissionSha256);

internal sealed record ScribeDescribeLatexRecord(
    string NodeId,
    string DefinitionPath,
    bool RequiresLatex,
    bool HasValidLatex);

internal sealed class VerifiedScribeEmissions
{
    private readonly ImmutableDictionary<string, ScribeEmissionRecord> records;
    private readonly ImmutableHashSet<string> declarationReferences;
    private readonly ImmutableArray<ScribeDescribeLatexRecord> describeLatexRecords;

    private VerifiedScribeEmissions(
        ImmutableDictionary<string, ScribeEmissionRecord> records,
        ImmutableHashSet<string> declarationReferences,
        ImmutableArray<ScribeDescribeLatexRecord> describeLatexRecords)
    {
        this.records = records;
        this.declarationReferences = declarationReferences;
        this.describeLatexRecords = describeLatexRecords;
    }

    internal static VerifiedScribeEmissions Empty { get; } = Create([], [], []);

    internal static VerifiedScribeEmissions Create(IEnumerable<ScribeEmissionRecord> values) =>
        Create(values, [], []);

    internal static VerifiedScribeEmissions Create(
        IEnumerable<ScribeEmissionRecord> values,
        IEnumerable<string> declarationReferences) =>
        Create(values, declarationReferences, []);

    internal static VerifiedScribeEmissions Create(
        IEnumerable<ScribeEmissionRecord> values,
        IEnumerable<string> declarationReferences,
        IEnumerable<ScribeDescribeLatexRecord> describeLatexRecords)
    {
        ArgumentNullException.ThrowIfNull(values);
        ArgumentNullException.ThrowIfNull(declarationReferences);
        ArgumentNullException.ThrowIfNull(describeLatexRecords);
        var records = values.ToArray();
        ScribeEmissionAttestation.ValidateRecords(records);
        var references = declarationReferences.ToImmutableHashSet(StringComparer.Ordinal);
        foreach (var reference in references)
        {
            if (!Gid.TryParse(reference, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                throw new FormatException(
                    $"verified Scribe declaration reference is not canonical: {reference}");
            }
        }

        var latexRecords = describeLatexRecords
            .OrderBy(static item => item.NodeId, StringComparer.Ordinal)
            .ToImmutableArray();
        var duplicateNode = latexRecords
            .GroupBy(static item => item.NodeId, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1);
        if (duplicateNode is not null)
        {
            throw new FormatException($"duplicate Scribe Describe node {duplicateNode.Key}");
        }
        foreach (var record in latexRecords)
        {
            var separator = record.NodeId.IndexOf("#describe/", StringComparison.Ordinal);
            var documentGid = separator > 0 ? record.NodeId[..separator] : string.Empty;
            if (!Gid.TryParse(documentGid, out _)
                || separator + "#describe/".Length == record.NodeId.Length
                || record.DefinitionPath != ScribeEmissionAttestation.DefinitionPath(documentGid))
            {
                throw new FormatException(
                    $"invalid Scribe Describe LaTeX coverage record {record.NodeId}");
            }
        }

        return new VerifiedScribeEmissions(
            records.ToImmutableDictionary(static item => item.Gid, StringComparer.Ordinal),
            references,
            latexRecords);
    }

    internal bool TryGet(string gid, out ScribeEmissionRecord record) =>
        records.TryGetValue(gid, out record!);

    internal bool ReferencesDeclaration(string gid) => declarationReferences.Contains(gid);

    internal ImmutableArray<ScribeDescribeLatexRecord> DescribeLatexRecords => describeLatexRecords;
}

internal sealed class ScribeEmissionAttestation
{
    internal const string RelativePath = "Meta/StrataLint/Generated/scribe-emissions.v1.json";

    private const string Schema = "scribe-emission-attestation-v1";

    private static readonly ImmutableHashSet<string> RootFields =
        ImmutableHashSet.Create(StringComparer.Ordinal, "entries", "schema");

    private static readonly ImmutableHashSet<string> EntryFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "definition_path",
        "definition_sha256",
        "emission_path",
        "emission_sha256",
        "gid");

    private readonly ImmutableDictionary<string, ScribeEmissionRecord> records;

    private ScribeEmissionAttestation(ImmutableDictionary<string, ScribeEmissionRecord> records) =>
        this.records = records;

    internal static ScribeEmissionAttestation Empty { get; } = new(
        ImmutableDictionary<string, ScribeEmissionRecord>.Empty.WithComparers(StringComparer.Ordinal));

    internal bool TryGet(string gid, out ScribeEmissionRecord record) =>
        records.TryGetValue(gid, out record!);

    internal static ImmutableArray<byte> Write(IEnumerable<ScribeEmissionRecord> values)
    {
        ArgumentNullException.ThrowIfNull(values);
        var records = values
            .OrderBy(static item => item.Gid, StringComparer.Ordinal)
            .ToArray();
        ValidateRecords(records);
        var material = new
        {
            schema = Schema,
            entries = records.Select(static item => new
            {
                gid = item.Gid,
                definition_path = item.DefinitionPath,
                definition_sha256 = item.DefinitionSha256,
                emission_path = item.EmissionPath,
                emission_sha256 = item.EmissionSha256,
            }),
        };
        return StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material));
    }

    internal static ScribeEmissionAttestation Load(
        RepositorySnapshot snapshot,
        ImmutableArray<string>.Builder findings)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(findings);
        if (!snapshot.TryGetFile(RelativePath, out var file))
        {
            return Empty;
        }

        try
        {
            using var document = JsonDocument.Parse(file.Text);
            if (!StructuredCanonicalWriter.WriteJson(document.RootElement).AsSpan()
                    .SequenceEqual(file.RawBytes.AsSpan()))
            {
                throw new FormatException("attestation is not canonical JSON");
            }

            RequireFields(document.RootElement, RootFields, "root");
            if (RequireString(document.RootElement, "schema") != Schema)
            {
                throw new FormatException($"schema must be {Schema}");
            }

            var entries = document.RootElement.GetProperty("entries");
            if (entries.ValueKind != JsonValueKind.Array)
            {
                throw new FormatException("entries must be an array");
            }

            var records = entries.EnumerateArray().Select(ParseRecord).ToArray();
            ValidateRecords(records);
            return new ScribeEmissionAttestation(records.ToImmutableDictionary(
                static item => item.Gid,
                StringComparer.Ordinal));
        }
        catch (Exception exception) when (exception is JsonException or FormatException or InvalidOperationException)
        {
            findings.Add($"{RelativePath} is invalid: {exception.Message}");
            return Empty;
        }
    }

    private static ScribeEmissionRecord ParseRecord(JsonElement element)
    {
        RequireFields(element, EntryFields, "entry");
        return new ScribeEmissionRecord(
            RequireString(element, "gid"),
            RequireString(element, "definition_path"),
            RequireString(element, "definition_sha256"),
            RequireString(element, "emission_path"),
            RequireString(element, "emission_sha256"));
    }

    internal static void ValidateRecords(IReadOnlyList<ScribeEmissionRecord> records)
    {
        var duplicate = records.GroupBy(static item => item.Gid, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1);
        if (duplicate is not null)
        {
            throw new FormatException($"duplicate Scribe emission GID {duplicate.Key}");
        }

        foreach (var record in records)
        {
            if (!Gid.TryParse(record.Gid, out _))
            {
                throw new FormatException($"invalid Scribe emission GID {record.Gid}");
            }

            var expectedDefinition = DefinitionPath(record.Gid);
            var expectedEmission = EmissionPath(record.Gid);
            if (record.DefinitionPath != expectedDefinition || record.EmissionPath != expectedEmission)
            {
                throw new FormatException($"noncanonical Scribe paths for {record.Gid}");
            }

            if (!DigestionFingerprint.IsCanonicalSha256(record.DefinitionSha256)
                || !DigestionFingerprint.IsCanonicalSha256(record.EmissionSha256))
            {
                throw new FormatException($"noncanonical Scribe fingerprint for {record.Gid}");
            }
        }
    }

    private static void RequireFields(
        JsonElement element,
        ImmutableHashSet<string> expected,
        string label)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{label} must be an object");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || actual.Distinct(StringComparer.Ordinal).Count() != actual.Length
            || actual.Any(name => !expected.Contains(name)))
        {
            throw new FormatException($"{label} fields are not the closed schema");
        }
    }

    private static string RequireString(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        return value.ValueKind == JsonValueKind.String
            ? value.GetString()!
            : throw new FormatException($"{property} must be a string");
    }

    internal static string DefinitionPath(string gid) => $"Blueprint/{gid}.scribe.cs";

    internal static string EmissionPath(string gid) => $"Blueprint/{gid}.md";

    internal static string DocumentGid(string coverageGid)
    {
        if (!Gid.TryParse(coverageGid, out var gid))
        {
            throw new FormatException($"invalid coverage GID {coverageGid}");
        }

        return gid.ToTarget() is Target.Formal formal
            ? Gid.FromTarget(formal with { Declaration = null }).Value
            : coverageGid;
    }
}
