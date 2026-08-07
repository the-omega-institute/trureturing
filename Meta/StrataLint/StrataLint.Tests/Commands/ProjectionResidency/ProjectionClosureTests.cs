using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Security.Cryptography;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ProjectionClosureTests
{
    private static readonly (string ScopeId, string ArtifactId)[] ExpectedScopes =
    [
        ("scope-a-anchor", "A-ANCHOR"),
        ("scope-a-dag", "A-DAG"),
        ("scope-a-echo", "A-ECHO"),
        ("scope-a-filemap", "A-FILEMAP"),
        ("scope-a-scribe", "A-SCRIBE"),
        ("scope-a-truth", "A-TRUTH"),
        ("scope-a-values", "A-VALUES"),
    ];

    [Fact]
    public void ExternalScopeAlphabetIsExactlyTheSpecSet()
    {
        Assert.Equal(ExpectedScopes, ProjectionClosureScopeCatalog.All);
        Assert.Equal(7, ProjectionClosureScopeCatalog.All.Length);
        Assert.Equal(7, ProjectionClosureScopeCatalog.All.Distinct().Count());
    }

    [Fact]
    public void MissingOrExtraScopeInAnyOfTheThreeSetsIsUnknown()
    {
        var complete = ExpectedScopes.Select(static item => item.ScopeId).ToImmutableArray();
        foreach (var removed in complete)
        {
            var shortSet = complete.Remove(removed);
            Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(shortSet, complete, complete));
            Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(complete, shortSet, complete));
            Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(complete, complete, shortSet));
        }

        var extra = complete.Add("scope-extra");
        Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(extra, complete, complete));
        Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(complete, extra, complete));
        Assert.Equal(3, ProjectionClosureValidator.ValidateScopeSets(complete, complete, extra));
        Assert.Equal(0, ProjectionClosureValidator.ValidateScopeSets(complete, complete, complete));
    }

    [Fact]
    public void InjectedExternalResultDigestMismatchIsUnknown()
    {
        Assert.Equal(3, ProjectionClosureValidator.ValidateInjectedDigest(
            new string('a', 64), new string('b', 64)));
        Assert.Equal(0, ProjectionClosureValidator.ValidateInjectedDigest(
            new string('a', 64), new string('a', 64)));
    }

    [Fact]
    public void ClosedOutputReaderRejectsExtraMissingReorderedAndDuplicateFields()
    {
        var canonical = ProjectionClosureTestFixture.CanonicalOutput(pass: true);
        var index = 0;
        foreach (var mutation in ProjectionClosureTestFixture.OutputSchemaMutations(canonical))
        {
            Assert.True(ProjectionClosureOutputReader.Validate(mutation) == 2, $"mutation {index}");
            index++;
        }
    }

    [Fact]
    public void OutputIsByteDeterministic()
    {
        var model = ProjectionClosureTestFixture.OutputModel(pass: true);
        Assert.Equal(ProjectionClosureWriter.Write(model), ProjectionClosureWriter.Write(model));
    }

    [Fact]
    public void RequiredHistoryBlocksPass()
    {
        var artifacts = ProjectionClosureTestFixture.Artifacts()
            .SetItem(0, ProjectionClosureTestFixture.Artifacts()[0] with
            {
                HistoryRequirement = "required",
            });
        Assert.False(ProjectionClosureValidator.CanPass(artifacts, boundariesValid: true));
    }

    [Fact]
    public void RegistryGovernanceDocumentsAreConsumersOfTheThreeProjections()
    {
        const string registry = """
            governance_documents:
              - "Generated/DAG.md"
              - "Generated/FILEMAP.md"
              - "Generated/echo-residual-summary.md"
            """;
        var found = RepositoryConsumerScanner.ScanRegistryGovernanceDocuments(
            Encoding.UTF8.GetBytes(registry));

        Assert.Equal(
            new[]
            {
                ("Generated/DAG.md", "Meta/registry.yaml", "registry:governance-documents"),
                ("Generated/FILEMAP.md", "Meta/registry.yaml", "registry:governance-documents"),
                ("Generated/echo-residual-summary.md", "Meta/registry.yaml", "registry:governance-documents"),
            },
            found.Select(static item => (item.ArtifactPath, item.ConsumerPath, item.Evidence)));

        foreach (var artifactPath in found.Select(static item => item.ArtifactPath))
        {
            var removed = registry.Replace($"- \"{artifactPath}\"", "", StringComparison.Ordinal);
            var rescanned = RepositoryConsumerScanner.ScanRegistryGovernanceDocuments(
                Encoding.UTF8.GetBytes(removed));
            Assert.Equal(
                3,
                ProjectionClosureValidator.ValidateKnownConsumers(found, rescanned));
        }
    }

    [Fact]
    public void CommandExecutesSevenQueriesHonorsInjectedDigestAndIsDeterministic()
    {
        lock (typeof(ProjectionClosureTests))
        {
            using var temporary = new TemporaryDirectory();
            var fixture = ProjectionClosureCommandFixture.Create(temporary.Path);
            var previousDigest = Environment.GetEnvironmentVariable("EXPECTED_EXTERNAL_SCOPE_RESULT_SHA256");
            var previousGate = Environment.GetEnvironmentVariable("EXPECTED_GATE_AUTHORITY_SHA256");
            var previousTime = Environment.GetEnvironmentVariable("P0_2_JUDGE_TIME");
            try
            {
                Environment.SetEnvironmentVariable("P0_2_JUDGE_TIME", "2026-08-07T00:00:00Z");
                Environment.SetEnvironmentVariable("EXPECTED_EXTERNAL_SCOPE_RESULT_SHA256", fixture.ResultDigest);
                Environment.SetEnvironmentVariable("EXPECTED_GATE_AUTHORITY_SHA256", new string('a', 64));
                var first = Path.Combine(temporary.Path, "first.json");
                var second = Path.Combine(temporary.Path, "second.json");
                var firstResult = ProjectionClosureCommand.Run(temporary.Path,
                    ["--manifest", fixture.ManifestPath, "--out", first]);
                Assert.True(firstResult.ExitCode == 0, firstResult.Error);
                var firstBytes = File.ReadAllBytes(first);
                Assert.True(ProjectionClosureOutputReader.Validate(firstBytes) == 0,
                    Encoding.UTF8.GetString(firstBytes));
                Assert.Equal(0, ProjectionClosureCommand.Run(temporary.Path,
                    ["--manifest", fixture.ManifestPath, "--out", second]).ExitCode);
                Assert.Equal(File.ReadAllBytes(first), File.ReadAllBytes(second));

                Environment.SetEnvironmentVariable("EXPECTED_EXTERNAL_SCOPE_RESULT_SHA256", new string('f', 64));
                Assert.Equal(3, ProjectionClosureCommand.Run(temporary.Path,
                    ["--manifest", fixture.ManifestPath, "--out", second]).ExitCode);
            }
            finally
            {
                Environment.SetEnvironmentVariable("EXPECTED_EXTERNAL_SCOPE_RESULT_SHA256", previousDigest);
                Environment.SetEnvironmentVariable("EXPECTED_GATE_AUTHORITY_SHA256", previousGate);
                Environment.SetEnvironmentVariable("P0_2_JUDGE_TIME", previousTime);
            }
        }
    }
}

internal static class ProjectionClosureTestFixture
{
    private static readonly string Sha = new('a', 64);

    internal static ImmutableArray<ProjectionClosureArtifact> Artifacts() =>
        ProjectionClosureScopeCatalog.All.Select(static item => new ProjectionClosureArtifact(
            item.ArtifactId,
            $"Generated/{item.ArtifactId}.json",
            "source",
            "Emitter",
            "run-local",
            ["verify"],
            [$"external:{item.ScopeId}"],
            "not-required",
            new string('a', 64))).ToImmutableArray();

    internal static ProjectionClosureOutput OutputModel(bool pass) => new(
        Sha,
        Artifacts(),
        Sha,
        [],
        Sha,
        [],
        [],
        [],
        pass);

    internal static byte[] CanonicalOutput(bool pass) => ProjectionClosureWriter.Write(OutputModel(pass));

    internal static IEnumerable<byte[]> OutputSchemaMutations(byte[] canonical)
    {
        var text = Encoding.UTF8.GetString(canonical);
        yield return Encoding.UTF8.GetBytes(text.Replace(
            "{\"artifact_set_sha256\":", "{\"extra\":true,\"artifact_set_sha256\":", StringComparison.Ordinal));
        yield return Encoding.UTF8.GetBytes(text.Replace(
            $"\"artifact_set_sha256\": \"{Sha}\", ", "", StringComparison.Ordinal));
        yield return Encoding.UTF8.GetBytes(text.Replace(
            $"{{\"artifact_set_sha256\": \"{Sha}\", \"artifacts\":",
            $"{{\"artifacts\": [], \"artifact_set_sha256\": \"{Sha}\", \"discard\":",
            StringComparison.Ordinal));
        yield return Encoding.UTF8.GetBytes(text.Replace(
            "{\"artifact_set_sha256\":", $"{{\"artifact_set_sha256\": \"{Sha}\", \"artifact_set_sha256\":", StringComparison.Ordinal));
    }
}

internal sealed record ProjectionClosureCommandFixture(string ManifestPath, string ResultDigest)
{
    internal static ProjectionClosureCommandFixture Create(string root)
    {
        Directory.CreateDirectory(Path.Combine(root, "Meta"));
        Directory.CreateDirectory(Path.Combine(root, "adapters"));
        File.WriteAllText(Path.Combine(root, "Meta", "registry.yaml"), """
            governance_documents:
              - "Generated/DAG.md"
              - "Generated/FILEMAP.md"
              - "Generated/echo-residual-summary.md"
            """, new UTF8Encoding(false));

        const string adapterBytes = "#!/bin/sh\nprintf result\n";
        var adapterSha = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(adapterBytes)));
        var resultSha = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes("result")));
        var attestations = ImmutableArray.CreateBuilder<JsonElement>();
        var attestationPaths = new List<string>();
        var authorityScopes = new List<object>();
        var externalTables = new StringBuilder();
        var fileTables = new StringBuilder();
        var pathByArtifact = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["A-ANCHOR"] = "Delta/anchor.json",
            ["A-DAG"] = "Generated/DAG.md",
            ["A-ECHO"] = "Generated/echo-residual-summary.md",
            ["A-FILEMAP"] = "Generated/FILEMAP.md",
            ["A-SCRIBE"] = "Zeta/scribe.json",
            ["A-TRUTH"] = "Zeta/truth.json",
            ["A-VALUES"] = "Zeta/values.json",
        };
        foreach (var (scopeId, artifactId) in ProjectionClosureScopeCatalog.All)
        {
            var adapter = $"adapters/{scopeId}.sh";
            var absoluteAdapter = Path.Combine(root, adapter);
            File.WriteAllText(absoluteAdapter, adapterBytes, new UTF8Encoding(false));
            if (!OperatingSystem.IsWindows())
            {
                File.SetUnixFileMode(absoluteAdapter,
                    UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            }
            authorityScopes.Add(new { scope_id = scopeId, artifact_id = artifactId, @namespace = scopeId,
                query_adapter = adapter, query_adapter_sha256 = adapterSha });
            externalTables.Append($"""

                [[external_scopes]]
                scope_id = "{scopeId}"
                artifact_id = "{artifactId}"
                namespace = "{scopeId}"
                query_adapter = "{adapter}"
                query_adapter_sha256 = "{adapterSha}"
                """);
            var consumers = pathByArtifact[artifactId].StartsWith("Generated/", StringComparison.Ordinal)
                ? $"[\"Meta/registry.yaml\", \"external:{scopeId}\"]"
                : $"[\"external:{scopeId}\"]";
            fileTables.Append($"""

                [[files]]
                pattern = "{pathByArtifact[artifactId]}"
                kind = "generated"
                produced_by = "Emitter"
                consumed_by = {consumers}
                verified_by = ["verify"]
                authority = "source"
                runtime_disposition = "run-local"
                artifact_id = "{artifactId}"
                """);
            var attestation = JsonSerializer.SerializeToElement(new { schema = "external-scope-attestation-v1",
                scope_id = scopeId, query_adapter_sha256 = adapterSha, query_result_sha256 = resultSha,
                observed_consumers = Array.Empty<string>(), issued_at = "2026-08-06T00:00:00Z",
                expires_at = "2026-08-08T00:00:00Z" });
            attestations.Add(attestation);
            var attestationPath = $"{scopeId}.json";
            File.WriteAllBytes(Path.Combine(root, attestationPath),
                JsonSerializer.SerializeToUtf8Bytes(attestation));
            attestationPaths.Add(attestationPath);
        }

        File.WriteAllText(Path.Combine(root, "candidate-filemap.toml"),
            "schema_version = 2\n\n[residence_policy]\ncase_id = \"X\"\ndesired = \"x\"\nknown_violation_count = 0\nstatus = \"active\"\n"
            + fileTables + externalTables + "\n", new UTF8Encoding(false));
        File.WriteAllBytes(Path.Combine(root, "authority.json"), JsonSerializer.SerializeToUtf8Bytes(
            new { schema = "external-scope-authority-v1", scopes = authorityScopes }));
        var manifestPath = Path.Combine(root, "manifest.json");
        File.WriteAllBytes(manifestPath, JsonSerializer.SerializeToUtf8Bytes(new
        {
            schema = "projection-closure-manifest-v1", filemap_path = "candidate-filemap.toml",
            external_scope_authority_path = "authority.json", attestation_paths = attestationPaths,
            expected_gate_authority_sha256 = new string('a', 64), obligations = Array.Empty<object>(),
            quotient_cases = Array.Empty<object>(), tripwires = Array.Empty<object>(),
        }));
        return new ProjectionClosureCommandFixture(manifestPath,
            ProjectionClosureCommand.ExternalResultDigestForTests(attestations.ToImmutable()));
    }
}
