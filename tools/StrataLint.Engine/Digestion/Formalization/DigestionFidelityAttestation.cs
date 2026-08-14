using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal enum DigestionFidelityClauseStatus
{
    Discharged,
    Undischarged,
}

internal enum DigestionFidelityGraderResult
{
    Pass,
    NotApplicable,
    Fail,
}

internal sealed record DigestionFidelityClause(
    string Key,
    int StartByte,
    int EndByte,
    string ClauseSha256);

internal sealed record DigestionFidelityClauseMapEntry(
    string ClauseKey,
    DigestionFidelityClauseStatus Status,
    string? Gid);

internal sealed record DigestionFidelityGraderTrap(
    string Trap,
    DigestionFidelityGraderResult Result);

internal sealed record DigestionFidelityAttestation(
    string AtomId,
    string TheoremGid,
    string SourceSha256,
    string DeclarationSha256,
    ImmutableArray<DigestionFidelityClause> Clauses,
    ImmutableArray<DigestionFidelityClauseMapEntry> ClauseMap,
    ImmutableArray<DigestionFidelityGraderTrap> GraderTraps,
    string AttestationSha256)
{
    internal const string Schema = "digestion-fidelity-attestation-v1";

    internal const string RootPath = "Meta/Digestion/fidelity-attestations/";

    internal const string PathSuffix = ".v1.json";

    internal static ImmutableArray<string> RequiredGraderTraps { get; } =
    [
        "conditional-vs-unconditional",
        "instance-vs-general",
        "mechanism-vs-outcome",
        "multi-clause-residue-names",
        "pointwise-vs-operator",
        "proof-internal-vs-addressable-statement",
        "witness-vs-universal",
    ];

    private static readonly ImmutableHashSet<string> RootFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "atom_id",
        "attestation_sha256",
        "clause_map",
        "clauses",
        "declaration_sha256",
        "grader_traps",
        "schema",
        "source_sha256",
        "theorem_gid");

    private static readonly ImmutableHashSet<string> ClauseFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "clause_sha256",
        "end_byte",
        "key",
        "start_byte");

    private static readonly ImmutableHashSet<string> DischargedMapFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "clause_key",
        "gid",
        "status");

    private static readonly ImmutableHashSet<string> UndischargedMapFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "clause_key",
        "status");

    private static readonly ImmutableHashSet<string> GraderTrapFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "result",
        "trap");

    internal static DigestionFidelityAttestation Create(
        string atomId,
        string theoremGid,
        string sourceSha256,
        string declarationSha256,
        ImmutableArray<DigestionFidelityClause> clauses,
        ImmutableArray<DigestionFidelityClauseMapEntry> clauseMap,
        ImmutableArray<DigestionFidelityGraderTrap> graderTraps)
    {
        var withoutAddress = new DigestionFidelityAttestation(
            atomId,
            theoremGid,
            sourceSha256,
            declarationSha256,
            clauses,
            clauseMap,
            graderTraps,
            string.Empty);
        var attestation = withoutAddress with
        {
            AttestationSha256 = ContentAddress(withoutAddress),
        };
        Validate(attestation);
        return attestation;
    }

    internal static string PathFor(string atomId, string theoremGid)
    {
        if (!IsCanonicalAtomId(atomId)
            || !Gid.TryParse(theoremGid, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: not null })
        {
            throw new FormatException("fidelity attestation key must contain a full atom id and theorem GID");
        }

        return RootPath + atomId + "/" + theoremGid + PathSuffix;
    }

    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(RootPath, StringComparison.Ordinal)
            || !path.EndsWith(PathSuffix, StringComparison.Ordinal))
        {
            return false;
        }

        var key = path[RootPath.Length..^PathSuffix.Length];
        var separator = key.IndexOf('/');
        return separator > 0
            && separator < key.Length - 1
            && IsCanonicalAtomId(key[..separator])
            && Gid.TryParse(key[(separator + 1)..], out var gid)
            && gid.ToTarget() is Target.Formal { Declaration: not null };
    }

    internal static ImmutableArray<byte> Write(DigestionFidelityAttestation attestation)
    {
        ArgumentNullException.ThrowIfNull(attestation);
        Validate(attestation);
        return StructuredCanonicalWriter.WriteJson(RootMaterial(attestation));
    }

    internal static DigestionFidelityAttestation Load(
        RepositorySnapshot snapshot,
        string relativePath)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentException.ThrowIfNullOrWhiteSpace(relativePath);
        if (!snapshot.TryGetFile(relativePath, out var file))
        {
            throw new FormatException($"digestion fidelity attestation is missing: {relativePath}");
        }

        try
        {
            using var document = JsonDocument.Parse(file.RawBytes.AsMemory());
            if (!StructuredCanonicalWriter.WriteJson(document.RootElement).AsSpan()
                    .SequenceEqual(file.RawBytes.AsSpan()))
            {
                throw new FormatException($"{relativePath} is not canonical JSON");
            }

            var root = document.RootElement;
            RequireFields(root, RootFields, "root");
            if (RequireString(root, "schema") != Schema)
            {
                throw new FormatException($"schema must be {Schema}");
            }

            var clauses = RequireArray(root, "clauses")
                .EnumerateArray()
                .Select(ReadClause)
                .ToImmutableArray();
            var clauseMap = RequireArray(root, "clause_map")
                .EnumerateArray()
                .Select(ReadClauseMapEntry)
                .ToImmutableArray();
            var graderTraps = RequireArray(root, "grader_traps")
                .EnumerateArray()
                .Select(ReadGraderTrap)
                .ToImmutableArray();
            var attestation = new DigestionFidelityAttestation(
                RequireString(root, "atom_id"),
                RequireString(root, "theorem_gid"),
                RequireString(root, "source_sha256"),
                RequireString(root, "declaration_sha256"),
                clauses,
                clauseMap,
                graderTraps,
                RequireString(root, "attestation_sha256"));
            Validate(attestation);
            if (!string.Equals(
                    relativePath,
                    PathFor(attestation.AtomId, attestation.TheoremGid),
                    StringComparison.Ordinal))
            {
                throw new FormatException(
                    "fidelity attestation path does not match its full atom id and theorem GID");
            }

            return attestation;
        }
        catch (JsonException exception)
        {
            throw new FormatException($"{relativePath} is not valid JSON", exception);
        }
    }

    private static void Validate(DigestionFidelityAttestation attestation)
    {
        if (!IsCanonicalAtomId(attestation.AtomId))
        {
            throw new FormatException("fidelity attestation atom_id is not canonical");
        }

        if (!Gid.TryParse(attestation.TheoremGid, out var theoremGid)
            || theoremGid.ToTarget() is not Target.Formal { Declaration: not null })
        {
            throw new FormatException("fidelity attestation theorem_gid must select a Lean declaration");
        }

        RequireSha256(attestation.SourceSha256, "source_sha256");
        RequireSha256(attestation.DeclarationSha256, "declaration_sha256");
        RequireSha256(attestation.AttestationSha256, "attestation_sha256");
        if (attestation.Clauses.IsDefaultOrEmpty)
        {
            throw new FormatException("fidelity attestation clauses must be a non-empty array");
        }

        if (!attestation.Clauses.SequenceEqual(
                attestation.Clauses.OrderBy(static clause => clause.Key, StringComparer.Ordinal)))
        {
            throw new FormatException("fidelity attestation clauses must be ordered by key");
        }

        var clauseKeys = new HashSet<string>(StringComparer.Ordinal);
        foreach (var clause in attestation.Clauses)
        {
            if (!IsCanonicalClauseKey(clause.Key) || !clauseKeys.Add(clause.Key))
            {
                throw new FormatException("fidelity attestation clause keys must be canonical and unique");
            }

            if (clause.StartByte < 0 || clause.EndByte <= clause.StartByte)
            {
                throw new FormatException("fidelity attestation clause span is malformed");
            }

            RequireSha256(clause.ClauseSha256, "clause_sha256");
        }

        if (!attestation.ClauseMap.SequenceEqual(
                attestation.ClauseMap.OrderBy(static item => item.ClauseKey, StringComparer.Ordinal)))
        {
            throw new FormatException("fidelity attestation clause_map must be ordered by clause_key");
        }

        var mappedKeys = new HashSet<string>(StringComparer.Ordinal);
        foreach (var item in attestation.ClauseMap)
        {
            if (!IsCanonicalClauseKey(item.ClauseKey) || !mappedKeys.Add(item.ClauseKey))
            {
                throw new FormatException("fidelity attestation clause_map keys must be canonical and unique");
            }

            switch (item.Status)
            {
                case DigestionFidelityClauseStatus.Discharged
                    when item.Gid is not null
                         && Gid.TryParse(item.Gid, out var gid)
                         && gid.ToTarget() is Target.Formal { Declaration: not null }:
                    break;
                case DigestionFidelityClauseStatus.Undischarged when item.Gid is null:
                    break;
                default:
                    throw new FormatException(
                        "fidelity attestation clause_map status/GID shape is invalid");
            }
        }

        if (!clauseKeys.SetEquals(mappedKeys))
        {
            throw new FormatException(
                "fidelity attestation clause_map is not exhaustive over its declared clauses");
        }

        if (!attestation.GraderTraps.SequenceEqual(
                attestation.GraderTraps.OrderBy(static item => item.Trap, StringComparer.Ordinal)))
        {
            throw new FormatException("fidelity attestation grader_traps must be ordered by trap");
        }

        var actualTraps = attestation.GraderTraps
            .Select(static item => item.Trap)
            .ToArray();
        if (!actualTraps.SequenceEqual(RequiredGraderTraps, StringComparer.Ordinal))
        {
            throw new FormatException(
                "fidelity attestation grader_traps must contain the exact required trap set");
        }

        if (attestation.GraderTraps.Any(static item => !Enum.IsDefined(item.Result)))
        {
            throw new FormatException("fidelity attestation grader trap result is invalid");
        }

        if (!string.Equals(
                attestation.AttestationSha256,
                ContentAddress(attestation),
                StringComparison.Ordinal))
        {
            throw new FormatException("fidelity attestation content address does not match its payload");
        }
    }

    private static string ContentAddress(DigestionFidelityAttestation attestation) =>
        DigestionFingerprint.Compute(
            StructuredCanonicalWriter.WriteJson(PayloadMaterial(attestation)).AsSpan()).RawSha256;

    private static JsonElement RootMaterial(DigestionFidelityAttestation attestation) =>
        JsonSerializer.SerializeToElement(new
        {
            atom_id = attestation.AtomId,
            attestation_sha256 = attestation.AttestationSha256,
            clause_map = attestation.ClauseMap.Select(ClauseMapMaterial),
            clauses = attestation.Clauses.Select(static clause => new
            {
                clause_sha256 = clause.ClauseSha256,
                end_byte = clause.EndByte,
                key = clause.Key,
                start_byte = clause.StartByte,
            }),
            declaration_sha256 = attestation.DeclarationSha256,
            grader_traps = attestation.GraderTraps.Select(static item => new
            {
                result = GraderResultText(item.Result),
                trap = item.Trap,
            }),
            schema = Schema,
            source_sha256 = attestation.SourceSha256,
            theorem_gid = attestation.TheoremGid,
        });

    private static JsonElement PayloadMaterial(DigestionFidelityAttestation attestation) =>
        JsonSerializer.SerializeToElement(new
        {
            atom_id = attestation.AtomId,
            clause_map = attestation.ClauseMap.Select(ClauseMapMaterial),
            clauses = attestation.Clauses.Select(static clause => new
            {
                clause_sha256 = clause.ClauseSha256,
                end_byte = clause.EndByte,
                key = clause.Key,
                start_byte = clause.StartByte,
            }),
            declaration_sha256 = attestation.DeclarationSha256,
            grader_traps = attestation.GraderTraps.Select(static item => new
            {
                result = GraderResultText(item.Result),
                trap = item.Trap,
            }),
            schema = Schema,
            source_sha256 = attestation.SourceSha256,
            theorem_gid = attestation.TheoremGid,
        });

    private static object ClauseMapMaterial(DigestionFidelityClauseMapEntry item) =>
        item.Status switch
        {
            DigestionFidelityClauseStatus.Discharged => new
            {
                clause_key = item.ClauseKey,
                gid = item.Gid,
                status = "discharged",
            },
            DigestionFidelityClauseStatus.Undischarged => new
            {
                clause_key = item.ClauseKey,
                status = "undischarged",
            },
            _ => throw new FormatException("fidelity attestation clause status is invalid"),
        };

    private static DigestionFidelityClause ReadClause(JsonElement element)
    {
        RequireFields(element, ClauseFields, "clause");
        return new DigestionFidelityClause(
            RequireString(element, "key"),
            RequireInt32(element, "start_byte"),
            RequireInt32(element, "end_byte"),
            RequireString(element, "clause_sha256"));
    }

    private static DigestionFidelityClauseMapEntry ReadClauseMapEntry(JsonElement element)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("clause_map entry must be an object");
        }

        var status = RequireString(element, "status");
        return status switch
        {
            "discharged" => ReadDischargedClauseMapEntry(element),
            "undischarged" => ReadUndischargedClauseMapEntry(element),
            _ => throw new FormatException("fidelity attestation clause_map status is invalid"),
        };
    }

    private static DigestionFidelityClauseMapEntry ReadDischargedClauseMapEntry(JsonElement element)
    {
        RequireFields(element, DischargedMapFields, "discharged clause_map entry");
        return new DigestionFidelityClauseMapEntry(
            RequireString(element, "clause_key"),
            DigestionFidelityClauseStatus.Discharged,
            RequireString(element, "gid"));
    }

    private static DigestionFidelityClauseMapEntry ReadUndischargedClauseMapEntry(JsonElement element)
    {
        RequireFields(element, UndischargedMapFields, "undischarged clause_map entry");
        return new DigestionFidelityClauseMapEntry(
            RequireString(element, "clause_key"),
            DigestionFidelityClauseStatus.Undischarged,
            null);
    }

    private static DigestionFidelityGraderTrap ReadGraderTrap(JsonElement element)
    {
        RequireFields(element, GraderTrapFields, "grader trap");
        var result = RequireString(element, "result") switch
        {
            "pass" => DigestionFidelityGraderResult.Pass,
            "not-applicable" => DigestionFidelityGraderResult.NotApplicable,
            "fail" => DigestionFidelityGraderResult.Fail,
            _ => throw new FormatException("fidelity attestation grader trap result is invalid"),
        };
        return new DigestionFidelityGraderTrap(RequireString(element, "trap"), result);
    }

    private static string GraderResultText(DigestionFidelityGraderResult result) => result switch
    {
        DigestionFidelityGraderResult.Pass => "pass",
        DigestionFidelityGraderResult.NotApplicable => "not-applicable",
        DigestionFidelityGraderResult.Fail => "fail",
        _ => throw new FormatException("fidelity attestation grader trap result is invalid"),
    };

    private static JsonElement RequireArray(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        return value.ValueKind == JsonValueKind.Array
            ? value
            : throw new FormatException($"{property} must be an array");
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
        if (!element.TryGetProperty(property, out var value)
            || value.ValueKind != JsonValueKind.String
            || string.IsNullOrWhiteSpace(value.GetString()))
        {
            throw new FormatException($"{property} must be a non-empty string");
        }

        return value.GetString()!;
    }

    private static int RequireInt32(JsonElement element, string property)
    {
        if (!element.TryGetProperty(property, out var value)
            || value.ValueKind != JsonValueKind.Number
            || !value.TryGetInt32(out var result))
        {
            throw new FormatException($"{property} must be an Int32");
        }

        return result;
    }

    private static void RequireSha256(string value, string field)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(value))
        {
            throw new FormatException($"{field} must be canonical sha256:<64 lowercase hex>");
        }
    }

    private static bool IsCanonicalAtomId(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && value.All(static character => character is
            (>= 'a' and <= 'z') or (>= '0' and <= '9') or '-');

    private static bool IsCanonicalClauseKey(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && value[0] is >= 'a' and <= 'z'
        && value.All(static character => character is
            (>= 'a' and <= 'z') or (>= '0' and <= '9') or '-');
}
