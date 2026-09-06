using System.Text;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed record ScribeTestMapEnvironment(
    string Rid,
    string Framework,
    string DotnetHost,
    string DotnetSdkVersion,
    string EvaluationEnvironmentDigest);

internal sealed record ScribeTestMapProducer(string EngineMvid)
{
    // Equal MVIDs for identical source under deterministic builds are a build artifact property.
    // CI must measure this; source inspection alone does not establish reproducibility.
    internal static ScribeTestMapProducer Current { get; } = new(
        typeof(ScribeTestMapDeriver).Assembly.ManifestModule.ModuleVersionId.ToString("N"));
}

internal sealed record ScribeTestMapEnvelope(
    int SchemaVersion,
    string InputDigest,
    string MetadataDigest,
    ScribeTestMapProducer Producer,
    ScribeTestMapEnvironment Environment,
    ScribeTestMap Map)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ScribeTestMapEnvelope Create(
        string inputDigest,
        string metadataDigest,
        ScribeTestMapEnvironment environment,
        ScribeTestMap map)
    {
        ArgumentNullException.ThrowIfNull(environment);
        ArgumentNullException.ThrowIfNull(map);
        if (!IsDigest(inputDigest))
        {
            throw new ArgumentException("Test-map input digest must be lowercase SHA-256 hex.", nameof(inputDigest));
        }

        if (!IsDigest(metadataDigest))
        {
            throw new ArgumentException("Test-map metadata digest must be lowercase SHA-256 hex.", nameof(metadataDigest));
        }

        return new ScribeTestMapEnvelope(
            1,
            inputDigest,
            metadataDigest,
            ScribeTestMapProducer.Current,
            environment,
            map);
    }

    internal byte[] Write()
    {
        var material = new
        {
            schema_version = SchemaVersion,
            input_digest = InputDigest,
            metadata_digest = MetadataDigest,
            producer = new
            {
                engine_mvid = Producer.EngineMvid,
            },
            environment = new
            {
                rid = Environment.Rid,
                framework = Environment.Framework,
                dotnet_host = Environment.DotnetHost,
                dotnet_sdk_version = Environment.DotnetSdkVersion,
                evaluation_environment_digest = Environment.EvaluationEnvironmentDigest,
            },
            map = new
            {
                methods = Map.Methods.Select(static method => new
                {
                    partition_key = method.PartitionKey,
                    source_path = method.SourcePath,
                    id = method.Id,
                    unknown_reasons = method.UnknownReasons.Select(static reason => reason.ToString()),
                }),
                unclassified_managed_project_paths = Map.UnclassifiedManagedProjectPaths,
                orphan_managed_source_paths = Map.OrphanManagedSourcePaths,
                dangling_compile_fail_proof_project_exemption_paths =
                    Map.DanglingCompileFailProofProjectExemptionPaths,
                compile_query_findings = Map.CompileQueryFindings.Select(static finding => new
                {
                    path = finding.Path,
                    message = finding.Message,
                }),
            },
        };
        return StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(material)).ToArray();
    }

    internal static bool TryRead(
        ReadOnlySpan<byte> bytes,
        out ScribeTestMapEnvelope? envelope,
        out string reason)
    {
        envelope = null;
        reason = string.Empty;
        try
        {
            var text = StrictUtf8.GetString(bytes);
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            RequireFields(root, "schema_version", "input_digest", "metadata_digest", "producer", "environment", "map");

            var schemaVersion = ReadInt32(root, "schema_version");
            if (schemaVersion != 1)
            {
                throw new EnvelopeReadException("schema-version");
            }

            var inputDigest = ReadString(root, "input_digest");
            if (!IsDigest(inputDigest))
            {
                throw new EnvelopeReadException("input-digest");
            }

            var metadataDigest = ReadString(root, "metadata_digest");
            if (!IsDigest(metadataDigest))
            {
                throw new EnvelopeReadException("metadata-digest");
            }

            var producerElement = root.GetProperty("producer");
            RequireFields(producerElement, "engine_mvid");
            var producer = new ScribeTestMapProducer(ReadString(producerElement, "engine_mvid"));
            if (!Guid.TryParseExact(producer.EngineMvid, "N", out var mvid)
                || !string.Equals(mvid.ToString("N"), producer.EngineMvid, StringComparison.Ordinal))
            {
                throw new EnvelopeReadException("producer");
            }

            var environmentElement = root.GetProperty("environment");
            RequireFields(environmentElement, "rid", "framework", "dotnet_host", "dotnet_sdk_version", "evaluation_environment_digest");
            var environment = new ScribeTestMapEnvironment(
                ReadString(environmentElement, "rid"),
                ReadString(environmentElement, "framework"),
                ReadString(environmentElement, "dotnet_host"),
                ReadString(environmentElement, "dotnet_sdk_version"),
                ReadString(environmentElement, "evaluation_environment_digest"));

            var map = ReadMap(root.GetProperty("map"));
            var canonical = StructuredCanonicalWriter.WriteJson(document.RootElement);
            if (!canonical.AsSpan().SequenceEqual(bytes))
            {
                throw new EnvelopeReadException("noncanonical");
            }

            envelope = new ScribeTestMapEnvelope(
                schemaVersion,
                inputDigest,
                metadataDigest,
                producer,
                environment,
                map);
            return true;
        }
        catch (EnvelopeReadException exception)
        {
            reason = exception.Reason;
            return false;
        }
        catch (DecoderFallbackException)
        {
            reason = "invalid-utf8";
            return false;
        }
        catch (Exception exception) when (exception is JsonException
            or FormatException
            or InvalidOperationException
            or OverflowException)
        {
            reason = "invalid-json";
            return false;
        }
    }

    private static ScribeTestMap ReadMap(JsonElement map)
    {
        RequireFields(
            map,
            "methods",
            "unclassified_managed_project_paths",
            "orphan_managed_source_paths",
            "dangling_compile_fail_proof_project_exemption_paths",
            "compile_query_findings");
        return new ScribeTestMap(
            ReadMethods(map.GetProperty("methods")),
            ReadStringList(map, "unclassified_managed_project_paths"),
            ReadStringList(map, "orphan_managed_source_paths"),
            ReadStringList(map, "dangling_compile_fail_proof_project_exemption_paths"),
            ReadFindings(map.GetProperty("compile_query_findings")));
    }

    private static IReadOnlyList<ScribeTestMethod> ReadMethods(JsonElement methods)
    {
        RequireArray(methods);
        var result = new List<ScribeTestMethod>();
        foreach (var method in methods.EnumerateArray())
        {
            RequireFields(method, "partition_key", "source_path", "id", "unknown_reasons");
            var reasonsElement = method.GetProperty("unknown_reasons");
            RequireArray(reasonsElement);
            var reasons = new List<TestMapUnknownReason>();
            foreach (var value in reasonsElement.EnumerateArray())
            {
                if (value.ValueKind != JsonValueKind.String
                    || value.GetString() is not { } name
                    || !Enum.TryParse<TestMapUnknownReason>(name, ignoreCase: false, out var parsed)
                    || !string.Equals(Enum.GetName(parsed), name, StringComparison.Ordinal))
                {
                    throw new EnvelopeReadException("unknown-reason");
                }

                reasons.Add(parsed);
            }

            result.Add(new ScribeTestMethod(
                ReadString(method, "partition_key"),
                ReadString(method, "source_path"),
                ReadString(method, "id"),
                reasons));
        }

        return result;
    }

    private static IReadOnlyList<MsBuildCompileFinding> ReadFindings(JsonElement findings)
    {
        RequireArray(findings);
        var result = new List<MsBuildCompileFinding>();
        foreach (var finding in findings.EnumerateArray())
        {
            RequireFields(finding, "path", "message");
            result.Add(new MsBuildCompileFinding(
                ReadString(finding, "path"),
                ReadString(finding, "message")));
        }

        return result;
    }

    private static IReadOnlyList<string> ReadStringList(JsonElement parent, string name)
    {
        var values = parent.GetProperty(name);
        RequireArray(values);
        return values.EnumerateArray().Select(ReadStringValue).ToArray();
    }

    private static string ReadString(JsonElement parent, string name) =>
        ReadStringValue(parent.GetProperty(name));

    private static string ReadStringValue(JsonElement value) =>
        value.ValueKind == JsonValueKind.String && value.GetString() is { } text
            ? text
            : throw new EnvelopeReadException("field");

    private static int ReadInt32(JsonElement parent, string name) =>
        parent.GetProperty(name).ValueKind == JsonValueKind.Number
        && parent.GetProperty(name).TryGetInt32(out var value)
            ? value
            : throw new EnvelopeReadException("field");

    private static void RequireArray(JsonElement value)
    {
        if (value.ValueKind != JsonValueKind.Array)
        {
            throw new EnvelopeReadException("field");
        }
    }

    private static void RequireFields(JsonElement value, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            throw new EnvelopeReadException("field");
        }

        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Length
            || actual.Distinct(StringComparer.Ordinal).Count() != actual.Length
            || !actual.Order(StringComparer.Ordinal).SequenceEqual(
                expected.Order(StringComparer.Ordinal),
                StringComparer.Ordinal))
        {
            throw new EnvelopeReadException("field");
        }
    }

    private static bool IsDigest(string value) =>
        value.Length == 64
        && value.AsSpan().IndexOfAnyExcept("0123456789abcdef") < 0;

    private sealed class EnvelopeReadException(string reason) : Exception
    {
        internal string Reason { get; } = reason;
    }
}
