using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Cli;

internal static class ProjectionClosureScopeCatalog
{
    internal static readonly ImmutableArray<(string ScopeId, string ArtifactId)> All =
    [
        ("scope-a-anchor", "A-ANCHOR"),
        ("scope-a-dag", "A-DAG"),
        ("scope-a-echo", "A-ECHO"),
        ("scope-a-filemap", "A-FILEMAP"),
        ("scope-a-scribe", "A-SCRIBE"),
        ("scope-a-truth", "A-TRUTH"),
        ("scope-a-values", "A-VALUES"),
    ];
}

internal sealed record ConsumerEvidence(string ArtifactPath, string ConsumerPath, string Evidence);

internal sealed record ProjectionClosureArtifact(
    string ArtifactId,
    string Path,
    string Authority,
    string Producer,
    string RuntimeDisposition,
    ImmutableArray<string> Verifiers,
    ImmutableArray<string> Consumers,
    string HistoryRequirement,
    string EvidenceSha256);

internal sealed record ProjectionClosureOutput(
    string FilemapSha256,
    ImmutableArray<ProjectionClosureArtifact> Artifacts,
    string ArtifactSetSha256,
    ImmutableArray<JsonElement> BoundaryAttestations,
    string ExpectedGateAuthoritySha256,
    ImmutableArray<JsonElement> Obligations,
    ImmutableArray<JsonElement> QuotientCases,
    ImmutableArray<JsonElement> Tripwires,
    bool Pass);

internal static class ProjectionClosureValidator
{
    internal static int ValidateScopeSets(
        IEnumerable<string> references,
        IEnumerable<string> projections,
        IEnumerable<string> authority)
    {
        var expected = ProjectionClosureScopeCatalog.All.Select(static item => item.ScopeId).ToArray();
        return EqualSet(references, expected) && EqualSet(projections, expected) && EqualSet(authority, expected)
            ? 0
            : 3;
    }

    internal static int ValidateInjectedDigest(string? injected, string recomputed) =>
        IsSha256(injected) && IsSha256(recomputed)
        && string.Equals(injected, recomputed, StringComparison.Ordinal)
            ? 0
            : 3;

    internal static int ValidateKnownConsumers(
        IEnumerable<ConsumerEvidence> expected,
        IEnumerable<ConsumerEvidence> actual) =>
        EqualSet(expected.Select(Key), actual.Select(Key)) ? 0 : 3;

    internal static bool CanPass(
        ImmutableArray<ProjectionClosureArtifact> artifacts,
        bool boundariesValid) =>
        boundariesValid
        && artifacts.Length == 7
        && artifacts.All(static item => item.HistoryRequirement == "not-required");

    internal static bool IsSha256(string? value) =>
        value is { Length: 64 } && value.All(static character =>
            character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static bool EqualSet(IEnumerable<string> left, IEnumerable<string> right)
    {
        var leftArray = left.Order(StringComparer.Ordinal).ToArray();
        var rightArray = right.Order(StringComparer.Ordinal).ToArray();
        return leftArray.Length == leftArray.Distinct(StringComparer.Ordinal).Count()
            && rightArray.Length == rightArray.Distinct(StringComparer.Ordinal).Count()
            && leftArray.SequenceEqual(rightArray, StringComparer.Ordinal);
    }

    private static string Key(ConsumerEvidence item) =>
        $"{item.ArtifactPath}\0{item.ConsumerPath}\0{item.Evidence}";
}

internal static class RepositoryConsumerScanner
{
    private static readonly string[] ProjectionPaths =
    [
        "Generated/DAG.md",
        "Generated/FILEMAP.md",
        "Generated/echo-residual-summary.md",
    ];

    internal static ImmutableArray<ConsumerEvidence> ScanRegistryGovernanceDocuments(
        ReadOnlySpan<byte> bytes)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(new UTF8Encoding(false, true).GetString(bytes)));
        if (stream.Documents.Count != 1
            || stream.Documents[0].RootNode is not YamlMappingNode root
            || !root.Children.TryGetValue(new YamlScalarNode("governance_documents"), out var node)
            || node is not YamlSequenceNode sequence)
        {
            return [];
        }

        return sequence.Children.OfType<YamlScalarNode>()
            .Select(static item => item.Value)
            .Where(static value => value is not null && ProjectionPaths.Contains(value, StringComparer.Ordinal))
            .Select(static value => new ConsumerEvidence(
                value!, "Meta/registry.yaml", "registry:governance-documents"))
            .OrderBy(static item => item.ArtifactPath, StringComparer.Ordinal)
            .ToImmutableArray();
    }
}

internal static class ProjectionClosureWriter
{
    internal static byte[] Write(ProjectionClosureOutput output) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            schema = "projection-closure-v1",
            filemap_sha256 = output.FilemapSha256,
            artifacts = output.Artifacts.Select(static item => new
            {
                artifact_id = item.ArtifactId,
                path = item.Path,
                authority = item.Authority,
                producer = item.Producer,
                runtime_disposition = item.RuntimeDisposition,
                verifiers = item.Verifiers,
                consumers = item.Consumers,
                history_requirement = item.HistoryRequirement,
                evidence_sha256 = item.EvidenceSha256,
            }),
            artifact_set_sha256 = output.ArtifactSetSha256,
            boundary_attestations = output.BoundaryAttestations,
            expected_gate_authority_sha256 = output.ExpectedGateAuthoritySha256,
            obligations = output.Obligations,
            quotient_cases = output.QuotientCases,
            tripwires = output.Tripwires,
            pass = output.Pass,
        })).ToArray();
}

internal static class ProjectionClosureOutputReader
{
    private static readonly string[] RootFields =
    [
        "artifact_set_sha256", "artifacts", "boundary_attestations",
        "expected_gate_authority_sha256", "filemap_sha256", "obligations", "pass",
        "quotient_cases", "schema", "tripwires",
    ];

    internal static int Validate(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var reader = new Utf8JsonReader(bytes, new JsonReaderOptions
            {
                AllowTrailingCommas = false,
                CommentHandling = JsonCommentHandling.Disallow,
            });
            if (!reader.Read() || reader.TokenType != JsonTokenType.StartObject)
            {
                return 2;
            }

            foreach (var expected in RootFields)
            {
                if (!reader.Read() || reader.TokenType != JsonTokenType.PropertyName
                    || reader.GetString() != expected || !reader.Read())
                {
                    return 2;
                }

                reader.Skip();
            }

            if (!reader.Read() || reader.TokenType != JsonTokenType.EndObject || reader.Read())
            {
                return 2;
            }

            using var document = JsonDocument.Parse(bytes.ToArray());
            return document.RootElement.GetProperty("schema").GetString() == "projection-closure-v1" ? 0 : 2;
        }
        catch (JsonException)
        {
            return 2;
        }
    }
}

internal sealed record ProjectionClosureManifest(
    string FilemapPath,
    string AuthorityPath,
    ImmutableArray<string> AttestationPaths,
    string ExpectedGateAuthoritySha256,
    ImmutableArray<JsonElement> Obligations,
    ImmutableArray<JsonElement> QuotientCases,
    ImmutableArray<JsonElement> Tripwires);

internal sealed record ExternalScopeBinding(
    string ScopeId,
    string ArtifactId,
    string Namespace,
    string QueryAdapter,
    string QueryAdapterSha256);

internal sealed record ClosureFileMap(
    ImmutableArray<ProjectionClosureArtifact> Artifacts,
    ImmutableArray<ExternalScopeBinding> Scopes);

internal static class ProjectionClosureCommand
{
    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 4 || arguments[0] != "--manifest" || arguments[2] != "--out")
        {
            return Usage();
        }

        try
        {
            var manifest = ParseManifest(File.ReadAllBytes(Resolve(repositoryRoot, arguments[1])));
            var injectedGateAuthority = Environment.GetEnvironmentVariable("EXPECTED_GATE_AUTHORITY_SHA256");
            if (ProjectionClosureValidator.ValidateInjectedDigest(
                injectedGateAuthority, manifest.ExpectedGateAuthoritySha256) != 0)
            {
                return new ExplicitCommandResult(2, string.Empty,
                    "P0_2_INVALID base-injected gate authority digest mismatch\n");
            }
            var filemapBytes = File.ReadAllBytes(Resolve(repositoryRoot, manifest.FilemapPath));
            var filemap = ParseFileMap(filemapBytes);
            var authorityBytes = File.ReadAllBytes(Resolve(repositoryRoot, manifest.AuthorityPath));
            var authority = ParseAuthority(authorityBytes);
            var references = filemap.Artifacts.SelectMany(static item => item.Consumers)
                .Where(static item => item.StartsWith("external:", StringComparison.Ordinal))
                .Select(static item => item["external:".Length..]);
            var scopeExit = ProjectionClosureValidator.ValidateScopeSets(
                references,
                filemap.Scopes.Select(static item => item.ScopeId),
                authority.Select(static item => item.ScopeId));
            if (scopeExit != 0 || !filemap.Scopes.SequenceEqual(authority))
            {
                return Unknown("external scope reference/projection/authority mismatch");
            }

            var attestations = manifest.AttestationPaths
                .Select(path => ParseAttestation(File.ReadAllBytes(Resolve(repositoryRoot, path))))
                .OrderBy(static item => item.GetProperty("scope_id").GetString(), StringComparer.Ordinal)
                .ToImmutableArray();
            if (attestations.Length != 7
                || !attestations.Select(static item => item.GetProperty("scope_id").GetString()!)
                    .SequenceEqual(ProjectionClosureScopeCatalog.All.Select(static item => item.ScopeId)))
            {
                return Unknown("attestation scope set mismatch");
            }

            if (!DateTimeOffset.TryParse(
                Environment.GetEnvironmentVariable("P0_2_JUDGE_TIME"),
                null,
                System.Globalization.DateTimeStyles.RoundtripKind,
                out var judgeTime))
            {
                return Unknown("base judge time missing or invalid");
            }

            for (var index = 0; index < attestations.Length; index++)
            {
                var binding = authority[index];
                var attestation = attestations[index];
                var adapterPath = Resolve(repositoryRoot, binding.QueryAdapter);
                if (attestation.GetProperty("query_adapter_sha256").GetString() != binding.QueryAdapterSha256
                    || Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(adapterPath))) != binding.QueryAdapterSha256
                    || RunQuery(adapterPath, binding.Namespace) != attestation.GetProperty("query_result_sha256").GetString()
                    || DateTimeOffset.Parse(attestation.GetProperty("expires_at").GetString()!, null,
                        System.Globalization.DateTimeStyles.RoundtripKind) <= judgeTime)
                {
                    return Unknown("attestation adapter binding or expiry invalid");
                }
            }

            var resultDigest = ExternalResultDigest(attestations);
            var injected = Environment.GetEnvironmentVariable("EXPECTED_EXTERNAL_SCOPE_RESULT_SHA256");
            if (ProjectionClosureValidator.ValidateInjectedDigest(injected, resultDigest) != 0)
            {
                return Unknown("base-injected external result digest mismatch");
            }

            var registryEvidence = RepositoryConsumerScanner.ScanRegistryGovernanceDocuments(
                File.ReadAllBytes(Path.Combine(repositoryRoot, "Meta/registry.yaml")));
            foreach (var evidence in registryEvidence)
            {
                var artifact = filemap.Artifacts.SingleOrDefault(item => item.Path == evidence.ArtifactPath);
                if (artifact is null || !artifact.Consumers.Contains(evidence.ConsumerPath, StringComparer.Ordinal))
                {
                    return Unknown($"unregistered consumer {evidence.ConsumerPath} for {evidence.ArtifactPath}");
                }
            }

            var artifacts = filemap.Artifacts.Select(item =>
            {
                var scopeId = item.Consumers.Single(value => value.StartsWith("external:", StringComparison.Ordinal))[9..];
                var attestation = attestations.Single(value => value.GetProperty("scope_id").GetString() == scopeId);
                return item with
                {
                    HistoryRequirement = RequiresHistory(attestation) ? "required" : "not-required",
                    EvidenceSha256 = EvidenceDigest(item, registryEvidence, attestations),
                };
            }).ToImmutableArray();
            var artifactSetSha = DomainDigest("artifact-set-v1", ArtifactBytes(artifacts));
            var pass = ProjectionClosureValidator.CanPass(artifacts, boundariesValid: true);
            var output = new ProjectionClosureOutput(
                Convert.ToHexStringLower(SHA256.HashData(filemapBytes)), artifacts, artifactSetSha,
                attestations, manifest.ExpectedGateAuthoritySha256, manifest.Obligations,
                manifest.QuotientCases, manifest.Tripwires, pass);
            var bytes = ProjectionClosureWriter.Write(output);
            File.WriteAllBytes(arguments[3], bytes);
            return new ExplicitCommandResult(pass ? 0 : 3, string.Empty, string.Empty);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or JsonException or FormatException or InvalidOperationException or TomlException)
        {
            return new ExplicitCommandResult(2, string.Empty, $"P0_2_INVALID {exception.Message}\n");
        }
    }

    private static ProjectionClosureManifest ParseManifest(byte[] bytes)
    {
        using var document = StrictObject(bytes, "manifest", [
            "schema", "filemap_path", "external_scope_authority_path", "attestation_paths",
            "expected_gate_authority_sha256", "obligations", "quotient_cases", "tripwires"]);
        var root = document.RootElement;
        if (root.GetProperty("schema").GetString() != "projection-closure-manifest-v1")
        {
            throw new FormatException("manifest schema invalid");
        }
        return new ProjectionClosureManifest(
            RequiredString(root, "filemap_path"), RequiredString(root, "external_scope_authority_path"),
            Strings(root, "attestation_paths"), RequiredSha(root, "expected_gate_authority_sha256"),
            Elements(root, "obligations"), Elements(root, "quotient_cases"), Elements(root, "tripwires"));
    }

    private static ImmutableArray<ExternalScopeBinding> ParseAuthority(byte[] bytes)
    {
        using var document = StrictObject(bytes, "authority", ["schema", "scopes"]);
        var root = document.RootElement;
        if (root.GetProperty("schema").GetString() != "external-scope-authority-v1")
            throw new FormatException("authority schema invalid");
        var values = root.GetProperty("scopes").EnumerateArray().Select(ParseScope).ToImmutableArray();
        if (!values.SequenceEqual(values.OrderBy(static item => item.ArtifactId, StringComparer.Ordinal)
            .ThenBy(static item => item.ScopeId, StringComparer.Ordinal)))
            throw new FormatException("authority scopes not sorted");
        return values;
    }

    private static JsonElement ParseAttestation(byte[] bytes)
    {
        using var document = StrictObject(bytes, "attestation", ["schema", "scope_id",
            "query_adapter_sha256", "query_result_sha256", "observed_consumers", "issued_at", "expires_at"]);
        var root = document.RootElement;
        if (root.GetProperty("schema").GetString() != "external-scope-attestation-v1"
            || !ProjectionClosureValidator.IsSha256(root.GetProperty("query_adapter_sha256").GetString())
            || !ProjectionClosureValidator.IsSha256(root.GetProperty("query_result_sha256").GetString()))
            throw new FormatException("attestation invalid");
        return root.Clone();
    }

    private static ClosureFileMap ParseFileMap(byte[] bytes)
    {
        var table = TomlSerializer.Deserialize<TomlTable>(new UTF8Encoding(false, true).GetString(bytes))
            ?? throw new FormatException("FILEMAP null");
        RequireKeys(table, "FILEMAP", "external_scopes", "files", "residence_policy", "schema_version");
        if (table["schema_version"] is not long schemaVersion || schemaVersion != 2
            || table["files"] is not TomlTableArray files
            || table["external_scopes"] is not TomlTableArray scopes)
            throw new FormatException("P0-2 candidate FILEMAP must be schema 2");
        var artifacts = files.Select(ParseArtifact).Where(static item => item.ArtifactId != "none")
            .OrderBy(static item => item.ArtifactId, StringComparer.Ordinal).ToImmutableArray();
        var bindings = scopes.Select(ParseScope).OrderBy(static item => item.ArtifactId, StringComparer.Ordinal)
            .ThenBy(static item => item.ScopeId, StringComparer.Ordinal).ToImmutableArray();
        if (artifacts.Length != 7 || artifacts.Select(static item => item.ArtifactId).Distinct().Count() != 7)
            throw new FormatException("FILEMAP artifact set invalid");
        return new ClosureFileMap(artifacts, bindings);
    }

    private static ProjectionClosureArtifact ParseArtifact(TomlTable value)
    {
        RequireKeys(value, "files entry", "artifact_id", "authority", "consumed_by", "kind", "pattern",
            "produced_by", "runtime_disposition", "verified_by");
        return new ProjectionClosureArtifact(S(value, "artifact_id"), S(value, "pattern"), S(value, "authority"),
            S(value, "produced_by"), S(value, "runtime_disposition"), A(value, "verified_by"),
            A(value, "consumed_by"), "not-required", new string('0', 64));
    }

    private static ExternalScopeBinding ParseScope(TomlTable value)
    {
        RequireKeys(value, "external scope", "artifact_id", "namespace", "query_adapter",
            "query_adapter_sha256", "scope_id");
        return new ExternalScopeBinding(S(value, "scope_id"), S(value, "artifact_id"), S(value, "namespace"),
            S(value, "query_adapter"), S(value, "query_adapter_sha256"));
    }

    private static ExternalScopeBinding ParseScope(JsonElement value)
    {
        RequireJsonKeys(value, ["scope_id", "artifact_id", "namespace", "query_adapter", "query_adapter_sha256"]);
        return new ExternalScopeBinding(RequiredString(value, "scope_id"), RequiredString(value, "artifact_id"),
            RequiredString(value, "namespace"), RequiredString(value, "query_adapter"), RequiredSha(value, "query_adapter_sha256"));
    }

    internal static string ExternalResultDigestForTests(ImmutableArray<JsonElement> attestations) =>
        ExternalResultDigest(attestations);

    private static string ExternalResultDigest(ImmutableArray<JsonElement> attestations)
    {
        var results = attestations.Select(item => new { scope_id = item.GetProperty("scope_id").GetString(),
            attestation_sha256 = DomainDigest("external-scope-attestation-v1",
                StructuredCanonicalWriter.WriteJson(item).ToArray()) });
        var bytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new { results })).ToArray();
        return DomainDigest("external-scope-results-v1", bytes);
    }

    private static string RunQuery(string adapterPath, string scopeNamespace)
    {
        var start = new ProcessStartInfo
        {
            FileName = adapterPath,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        start.ArgumentList.Add(scopeNamespace);
        using var process = Process.Start(start) ?? throw new IOException("query adapter did not start");
        using var output = new MemoryStream();
        process.StandardOutput.BaseStream.CopyTo(output);
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0)
            throw new InvalidOperationException($"query adapter failed: {error}");
        return Convert.ToHexStringLower(SHA256.HashData(output.ToArray()));
    }

    private static bool RequiresHistory(JsonElement attestation)
    {
        var observed = attestation.GetProperty("observed_consumers");
        if (observed.ValueKind != JsonValueKind.Array)
            throw new FormatException("observed_consumers must be an array");
        return observed.EnumerateArray().Any(static consumer => consumer.ValueKind switch
        {
            JsonValueKind.String => false,
            JsonValueKind.Object => consumer.TryGetProperty("history_requirement", out var requirement)
                && requirement.GetString() switch
                {
                    "required" => true,
                    "not-required" => false,
                    _ => throw new FormatException("consumer history_requirement invalid"),
                },
            _ => throw new FormatException("observed consumer invalid"),
        });
    }

    private static byte[] ArtifactBytes(ImmutableArray<ProjectionClosureArtifact> artifacts) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(artifacts)).ToArray();
    private static string EvidenceDigest(ProjectionClosureArtifact artifact,
        ImmutableArray<ConsumerEvidence> registry, ImmutableArray<JsonElement> attestations) =>
        DomainDigest("artifact-consumer-evidence-v1", StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(new { artifact.ArtifactId,
                registry = registry.Where(item => item.ArtifactPath == artifact.Path),
                attestation = attestations.Single(item => item.GetProperty("scope_id").GetString()
                    == artifact.Consumers.Single(value => value.StartsWith("external:", StringComparison.Ordinal))[9..]) })).ToArray());
    private static string DomainDigest(string domain, byte[] bytes) => Convert.ToHexStringLower(
        SHA256.HashData(Encoding.UTF8.GetBytes(domain).Concat([(byte)0]).Concat(bytes).ToArray()));
    private static string Resolve(string root, string path) => Path.IsPathRooted(path) ? path : Path.Combine(root, path);
    private static ExplicitCommandResult Unknown(string message) => new(3, string.Empty, $"P0_2_UNKNOWN {message}\n");
    private static ExplicitCommandResult Usage() => new(2, string.Empty,
        "USAGE: StrataLint projection-closure --manifest FILE --out FILE\n");

    private static JsonDocument StrictObject(byte[] bytes, string label, string[] keys)
    {
        var document = JsonDocument.Parse(bytes, new JsonDocumentOptions { AllowTrailingCommas = false, CommentHandling = JsonCommentHandling.Disallow });
        RequireJsonKeys(document.RootElement, keys);
        return document;
    }
    private static void RequireJsonKeys(JsonElement value, string[] keys)
    {
        if (value.ValueKind != JsonValueKind.Object || !value.EnumerateObject().Select(static p => p.Name).SequenceEqual(keys))
            throw new FormatException("JSON object fields missing, extra, reordered, or duplicate");
    }
    private static string RequiredString(JsonElement root, string key) => root.GetProperty(key).GetString() is { Length: > 0 } value ? value : throw new FormatException($"{key} invalid");
    private static string RequiredSha(JsonElement root, string key) { var value = RequiredString(root, key); return ProjectionClosureValidator.IsSha256(value) ? value : throw new FormatException($"{key} invalid"); }
    private static ImmutableArray<string> Strings(JsonElement root, string key) => root.GetProperty(key).EnumerateArray().Select(static item => item.GetString() ?? throw new FormatException("string array invalid")).ToImmutableArray();
    private static ImmutableArray<JsonElement> Elements(JsonElement root, string key) => root.GetProperty(key).EnumerateArray().Select(static item => item.Clone()).ToImmutableArray();
    private static void RequireKeys(TomlTable table, string label, params string[] keys) { if (!table.Keys.Order(StringComparer.Ordinal).SequenceEqual(keys.Order(StringComparer.Ordinal))) throw new FormatException($"{label} keys invalid"); }
    private static string S(TomlTable table, string key) => table[key] as string ?? throw new FormatException($"{key} invalid");
    private static ImmutableArray<string> A(TomlTable table, string key) => table[key] is TomlArray array ? array.Select(item => item as string ?? throw new FormatException($"{key} invalid")).ToImmutableArray() : throw new FormatException($"{key} invalid");
}
