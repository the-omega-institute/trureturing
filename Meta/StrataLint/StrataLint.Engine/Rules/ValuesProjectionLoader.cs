using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record ValuesProjectionDefinition(
    string Id,
    string Status,
    string LeanGid,
    string LeanStatementSha256);

internal sealed class ValuesProjection
{
    internal ValuesProjection(ImmutableDictionary<string, ValuesProjectionDefinition> definitions) =>
        Definitions = definitions;

    internal ImmutableDictionary<string, ValuesProjectionDefinition> Definitions { get; }
}

internal static class ValuesProjectionLoader
{
    internal const string RelativePath = "Evidence/D5/values.json";
    internal const string InputPath = "D5/X_Frontier/ValuesProducer.lean";
    internal const string LeanModulePath = "D5/S3/Constants/Values.lean";
    internal const string KernelDataPath =
        "Meta/StrataLint/Golden/values-kernels.toml";
    internal const string ScribeLockPath =
        "Meta/StrataLint/StrataLint.Scribe/packages.lock.json";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex Sha256Pattern = new("^[0-9a-f]{64}$", RegexOptions.CultureInvariant);
    internal static ImmutableArray<string> InputPaths { get; } =
    [
        LeanModulePath,
        InputPath,
        "Directory.Build.props",
        "Directory.Packages.props",
        KernelDataPath,
        ScribeLockPath,
        "global.json",
    ];
    private static readonly ImmutableArray<string> ExpectedIds =
    [
        "D5/Ah", "D5/Bh", "D5/C0", "D5/Cphi", "D5/E", "D5/T0", "D5/T1",
        "D5/c1", "D5/c2", "D5/cstar", "D5/delta.mean", "D5/hbar", "D5/kappa", "D5/s1",
    ];

    internal static ValuesProjection Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        if (!snapshot.TryGetFile(RelativePath, out var file))
        {
            throw new FormatException("Canonical values projection is missing.");
        }

        using var document = JsonDocument.Parse(file.Text);
        var canonical = StructuredCanonicalWriter.WriteJson(document.RootElement);
        if (!file.RawBytes.AsSpan().SequenceEqual(canonical.AsSpan()))
        {
            throw new FormatException("Values projection bytes are not canonical.");
        }

        var root = document.RootElement;
        if (root.ValueKind != JsonValueKind.Object
            || !PropertyNames(root).SequenceEqual(
                ["attestation", "constants", "schema_version"],
                StringComparer.Ordinal)
            || root.GetProperty("schema_version").ValueKind != JsonValueKind.Number
            || root.GetProperty("schema_version").GetInt32() != 2
            || root.GetProperty("constants").ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("Values projection root schema is invalid.");
        }

        var definitions = ParseDefinitions(root.GetProperty("constants"));
        ValidateAttestation(snapshot, root.GetProperty("attestation"), definitions);
        return new ValuesProjection(definitions);
    }

    private static void ValidateAttestation(
        RepositorySnapshot snapshot,
        JsonElement attestation,
        ImmutableDictionary<string, ValuesProjectionDefinition> definitions)
    {
        if (attestation.ValueKind != JsonValueKind.Object
            || !PropertyNames(attestation).SequenceEqual(
                ["consistency", "emitter", "emitter_version", "input_sha256", "inputs", "projection", "provenance"],
                StringComparer.Ordinal)
            || RequiredString(attestation, "emitter") != "StrataLint.Scribe.ValuesProducer"
            || attestation.GetProperty("emitter_version").ValueKind != JsonValueKind.Number
            || attestation.GetProperty("emitter_version").GetInt32() != 2
            || RequiredString(attestation, "projection") != "D5/E/values--json"
            || attestation.GetProperty("inputs").ValueKind != JsonValueKind.Array
            || attestation.GetProperty("provenance").ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("Values producer attestation schema is invalid.");
        }

        var consistency = attestation.GetProperty("consistency");
        if (consistency.ValueKind != JsonValueKind.Object
            || !PropertyNames(consistency).SequenceEqual(
                ["lean_binding", "numeric_binding"],
                StringComparer.Ordinal)
            || RequiredString(consistency, "lean_binding")
                != "gid+kind=def+std3+statement-sha256"
            || RequiredString(consistency, "numeric_binding")
                != "not-kernel-evaluated:noncomputable-real")
        {
            throw new FormatException("Values consistency boundary is invalid.");
        }

        var provenance = attestation.GetProperty("provenance").EnumerateArray()
            .Select(static item => item.ValueKind == JsonValueKind.String ? item.GetString() : null)
            .ToArray();
        if (provenance.Any(string.IsNullOrWhiteSpace)
            || !provenance.SequenceEqual(
                definitions.Values.OrderBy(static item => item.Id, StringComparer.Ordinal)
                    .Select(static item => item.LeanGid),
                StringComparer.Ordinal))
        {
            throw new FormatException("Values producer provenance must be the complete Lean GID list.");
        }

        ValidateInputAttestation(snapshot, attestation);
    }

    private static void ValidateInputAttestation(
        RepositorySnapshot snapshot,
        JsonElement attestation)
    {
        var inputs = attestation.GetProperty("inputs").EnumerateArray().ToArray();
        if (inputs.Length != InputPaths.Length)
        {
            throw new FormatException("Values producer input manifest is invalid.");
        }

        var verifiedInputs = new (string Path, string Sha256)[inputs.Length];
        for (var index = 0; index < inputs.Length; index++)
        {
            var input = inputs[index];
            var expectedPath = InputPaths[index];
            if (input.ValueKind != JsonValueKind.Object
                || !PropertyNames(input).SequenceEqual(["path", "sha256"], StringComparer.Ordinal)
                || RequiredString(input, "path") != expectedPath)
            {
                throw new FormatException("Values producer input manifest is invalid.");
            }

            var declaredSha = RequiredString(input, "sha256");
            if (!Sha256Pattern.IsMatch(declaredSha)
                || !snapshot.TryGetFile(expectedPath, out var source))
            {
                throw new FormatException("Values producer input SHA-256 cannot be verified.");
            }

            var actualSha = Convert.ToHexStringLower(SHA256.HashData(source.RawBytes.AsSpan()));
            if (!string.Equals(declaredSha, actualSha, StringComparison.Ordinal))
            {
                throw new FormatException("Values producer input SHA-256 does not match the repository input.");
            }

            verifiedInputs[index] = (expectedPath, actualSha);
        }

        var declaredCombined = RequiredString(attestation, "input_sha256");
        if (!Sha256Pattern.IsMatch(declaredCombined)
            || !string.Equals(
                declaredCombined,
                CombinedInputSha256(verifiedInputs),
                StringComparison.Ordinal))
        {
            throw new FormatException("Values producer input SHA-256 does not match the repository input.");
        }
    }

    private static ImmutableDictionary<string, ValuesProjectionDefinition> ParseDefinitions(
        JsonElement constants)
    {
        var definitions = ImmutableDictionary.CreateBuilder<string, ValuesProjectionDefinition>(
            StringComparer.Ordinal);
        var elements = constants.EnumerateArray().ToArray();
        if (elements.Length != ExpectedIds.Length)
        {
            throw new FormatException("Values projection must contain exactly fourteen constants.");
        }

        foreach (var (element, index) in elements.Select((value, index) => (value, index)))
        {
            ValidateDefinitionShape(element);
            var id = RequiredString(element, "id");
            var status = RequiredString(element, "status");
            var leanGid = RequiredString(element, "lean_gid");
            var statementSha = RequiredString(element, "lean_statement_sha256");
            if (!string.Equals(id, ExpectedIds[index], StringComparison.Ordinal)
                || !Gid.TryParse(leanGid, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null }
                || !Sha256Pattern.IsMatch(statementSha)
                || RequiredString(element, "provenance") != leanGid
                || !definitions.TryAdd(
                    id,
                    new ValuesProjectionDefinition(id, status, leanGid, statementSha)))
            {
                throw new FormatException(
                    "Values constants need unique sorted ids and concrete Lean declaration provenance.");
            }

            ValidateDefinitionState(element, id, status);
        }

        return definitions.ToImmutable();
    }

    private static void ValidateDefinitionShape(JsonElement element)
    {
        var expected = new[]
        {
            "comparison", "decimal", "definition", "error", "exact_value", "formula", "id",
            "kernel_receipts", "lean_gid", "lean_statement_sha256", "method", "open_reason",
            "provenance", "reference_error", "reference_value", "refs", "status", "value",
        };
        if (element.ValueKind != JsonValueKind.Object
            || !PropertyNames(element).SequenceEqual(expected, StringComparer.Ordinal)
            || element.GetProperty("kernel_receipts").ValueKind != JsonValueKind.Array
            || element.GetProperty("refs").ValueKind != JsonValueKind.Object
            || PropertyNames(element.GetProperty("refs")).Any(name =>
                element.GetProperty("refs").GetProperty(name).ValueKind != JsonValueKind.String)
            || !IsOptionalString(element.GetProperty("formula"))
            || !IsOptionalString(element.GetProperty("exact_value")))
        {
            throw new FormatException("Values constant schema is invalid.");
        }

        _ = RequiredString(element, "comparison");
        _ = RequiredString(element, "definition");
        _ = RequiredString(element, "method");
        _ = RequiredString(element, "provenance");
        _ = RequiredString(element, "reference_error");
        _ = RequiredString(element, "reference_value");
    }

    private static void ValidateDefinitionState(JsonElement element, string id, string status)
    {
        var receipts = element.GetProperty("kernel_receipts").EnumerateArray().ToArray();
        var kernels = receipts.Select(ValidateReceipt).ToArray();
        if (kernels.Distinct(StringComparer.Ordinal).Count() != kernels.Length)
        {
            throw new FormatException($"Values constant {id} repeats a kernel receipt.");
        }

        if (status == "registered-open")
        {
            if (RequiredString(element, "comparison") != "not-computed-open"
                || !IsNull(element, "decimal")
                || !IsNull(element, "error")
                || !IsNull(element, "value")
                || OptionalString(element, "open_reason") is null
                || receipts.Length != 0)
            {
                throw new FormatException($"Registered-open values constant {id} claims computed material.");
            }

            return;
        }

        if (status != "emitted"
            || OptionalString(element, "decimal") is null
            || OptionalString(element, "error") is null
            || OptionalString(element, "value") is null
            || !IsNull(element, "open_reason"))
        {
            throw new FormatException($"Emitted values constant {id} has an invalid state.");
        }

        var expectedKernels = id == "D5/Cphi"
            ? new[] { "exact-fractional-parts", "neumaier-summation", "full-period-window-average" }
            : new[] { "exact-quadratic" };
        if (!kernels.SequenceEqual(expectedKernels, StringComparer.Ordinal)
            || id == "D5/Cphi"
                && RequiredString(element, "comparison") != "reference-mismatch-open"
            || id != "D5/Cphi"
                && RequiredString(element, "comparison") != "reference-exact")
        {
            throw new FormatException($"Emitted values constant {id} has invalid kernel receipts.");
        }
    }

    private static string ValidateReceipt(JsonElement receipt)
    {
        if (receipt.ValueKind != JsonValueKind.Object
            || !PropertyNames(receipt).SequenceEqual(["kernel", "parameters", "results"], StringComparer.Ordinal)
            || receipt.GetProperty("parameters").ValueKind != JsonValueKind.Object
            || receipt.GetProperty("results").ValueKind != JsonValueKind.Object
            || !PropertyNames(receipt.GetProperty("parameters")).Any())
        {
            throw new FormatException("Values kernel receipt schema is invalid.");
        }

        foreach (var mapping in new[] { receipt.GetProperty("parameters"), receipt.GetProperty("results") })
        {
            if (mapping.EnumerateObject().Any(static property =>
                property.Value.ValueKind != JsonValueKind.String
                || string.IsNullOrWhiteSpace(property.Value.GetString())))
            {
                throw new FormatException("Values kernel receipt fields must be non-empty strings.");
            }
        }

        return RequiredString(receipt, "kernel");
    }

    private static string CombinedInputSha256(
        IEnumerable<(string Path, string Sha256)> inputs)
    {
        var material = "stratalint-scribe-values-input-v2\0" + string.Concat(
            inputs.Select(static input => input.Path + "\0" + input.Sha256 + "\n"));
        return Convert.ToHexStringLower(SHA256.HashData(StrictUtf8.GetBytes(material)));
    }

    private static IEnumerable<string> PropertyNames(JsonElement element) =>
        element.EnumerateObject().Select(static property => property.Name);

    private static string RequiredString(JsonElement element, string property) =>
        OptionalString(element, property)
        ?? throw new FormatException($"Values property {property} must be a non-empty string.");

    private static string? OptionalString(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        return value.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(value.GetString())
            ? value.GetString()
            : null;
    }

    private static bool IsOptionalString(JsonElement element) =>
        element.ValueKind == JsonValueKind.Null
        || element.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(element.GetString());

    private static bool IsNull(JsonElement element, string property) =>
        element.GetProperty(property).ValueKind == JsonValueKind.Null;
}
