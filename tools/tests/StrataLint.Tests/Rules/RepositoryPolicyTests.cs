using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RepositoryPolicyTests
{
    private static PolicyLoadOutcome Load(string fileMap, string? domains = null) =>
        RepositoryPolicyLoader.Load(Encoding.UTF8.GetBytes(fileMap), Encoding.UTF8.GetBytes(domains ?? TestFileMap.Domains));

    [Fact]
    public void ValidatedPolicyHasPrivateConstructionAndStableSemanticIdentity()
    {
        var first = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        var second = PolicyLoadAssert.Accepted(Load("# formatting is not policy\n" + TestFileMap.Canonical)).Policy;
        var third = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            first.CanonicalFileMapBytes.AsSpan(), first.CanonicalDomainsBytes.AsSpan())).Policy;
        Assert.Empty(typeof(ValidatedPolicy).GetConstructors());
        Assert.Equal(7, first.ArtifactKinds.Count);
        Assert.Equal(4, first.Domains.Count);
        Assert.Equal(first.FileMapSha256, second.FileMapSha256);
        Assert.Equal(first.FileMapSha256, third.FileMapSha256);
        Assert.Equal(TestFileMap.Canonical, Encoding.UTF8.GetString(first.CanonicalFileMapBytes.AsSpan()));
    }

    [Fact]
    public void CurrentRepositoryPolicyHasCanonicalBytesAndPreservesReservedFormats()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, "Meta/FILEMAP.toml"));
        var domains = File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"));
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(bytes, domains)).Policy;
        Assert.Equal(bytes, policy.CanonicalFileMapBytes.ToArray());
        Assert.Equal(["csv", "json", "md", "py", "txt", "yaml", "yml"],
            policy.ArtifactKinds.Keys.Select(k => k.Value).Order(StringComparer.Ordinal).ToArray());
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("LICENSE"), policy));
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("unregistered.json"), policy));
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("agents/unregistered.md"), policy));
    }

    [Theory]
    [InlineData("csv", "result", "opaque-text")]
    [InlineData("json", "run", "structured-json")]
    [InlineData("md", "result", "opaque-text")]
    [InlineData("py", "source", "opaque-text")]
    [InlineData("txt", "result", "opaque-text")]
    [InlineData("yaml", "spec", "structured-yaml")]
    [InlineData("yml", "spec", "structured-yaml")]
    public void EveryEvidenceFormatRoutesAndDecodesThroughFileMap(string kind, string selector, string profile)
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        var routed = Assert.IsType<RouteOutcome.Routed>(RouteEngine.Route(policy,
            new ManifestSyntax("D5", "E", "Carrier", "Sample", "E", selector, kind, "")));
        Assert.Equal($"Evidence/D5/S0/Carrier/Sample.{selector}.{kind}", routed.Result.Path.Value);
        Assert.True(RepositoryPathPolicy.TryResolve(routed.Result.Path, policy, out var reverse));
        Assert.Equal(routed.Result.Gid, reverse);
        Assert.True(RepositoryPathPolicy.TryGetValidationProfile(routed.Result.Path, policy, out var actual));
        Assert.Equal(profile, actual);
    }

    [Theory]
    [InlineData("csv", "experiments/D5-X0001", "result", false)]
    [InlineData("json", "experiments/D5-X0001", "run", true)]
    [InlineData("json", "kernels/Demo", "check", true)]
    [InlineData("json", "X_Frontier/Demo", "quote", true)]
    [InlineData("md", "X_Frontier/Demo", "result", true)]
    [InlineData("py", "kernels/Demo", "source", true)]
    [InlineData("txt", "kernels/Demo", "result", false)]
    [InlineData("yaml", "experiments/D5-X0001", "spec", true)]
    [InlineData("yml", "experiments/D5-X0001", "run", true)]
    [InlineData("json", "S0/Carrier/Demo", "source", false)]
    [InlineData("json", "S1/Carrier/Demo", "result", false)]
    [InlineData("json", "S0/Unknown/Demo", "result", false)]
    public void EvidenceSelectorsScopesAndDomainsAreConjunctive(string kind, string coordinate, string selector, bool allowed)
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        var issue = RepositoryPathPolicy.Validate(RepoPath.CreateKnown($"Evidence/D5/{coordinate}.{selector}.{kind}"), policy);
        Assert.Equal(allowed, issue is null);
    }

    [Theory]
    [InlineData("schema_version = 3", "schema_version = 2", "schema_version")]
    [InlineData("schema_version = 3", "schema_version = 3\nunknown = true", "unknown")]
    [InlineData("schema_version = 3", "schema_version = 3\nschema_version = 3", "TOML")]
    [InlineData("profile = \"structured-json\"", "profile = \"structured-json\"\nprofile = \"opaque-text\"", "TOML")]
    [InlineData("profile = \"structured-json\"", "profile = \"unknown\"", "profile")]
    [InlineData("profile = \"structured-json\"", "profile = 1", "profile")]
    [InlineData("profile = \"structured-json\"", "", "missing")]
    [InlineData("selectors = [\"source\"]", "selectors = []", "selectors")]
    [InlineData("selectors = [\"source\"]", "selectors = [\"source\", \"Source\"]", "case-colliding")]
    [InlineData("selectors = [\"source\"]", "selectors = [\"source\", \"source\"]", "duplicate")]
    [InlineData("selectors = [\"source\"]", "selectors = [\"../source\"]", "invalid")]
    [InlineData("path_selectors = [\"formal\", \"kernels\"]", "path_selectors = [\"unknown\"]", "path_selectors")]
    [InlineData("digestion_source = true", "digestion_source = false", "digestion_source")]
    public void MalformedFileMapFailsClosed(string before, string after, string marker)
    {
        Assert.Contains(before, TestFileMap.Canonical, StringComparison.Ordinal);
        var failure = Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(TestFileMap.Canonical.Replace(before, after, StringComparison.Ordinal)));
        Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
        var thrown = Assert.ThrowsAny<Exception>(() => PolicyLoadAssert.Accepted(failure));
        Assert.Contains(marker, thrown.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MissingEvidenceAndCaseCollidingKindsFailClosed()
    {
        var text = TestFileMap.Canonical;
        var start = text.IndexOf("[evidence.", StringComparison.Ordinal);
        var end = text.IndexOf("[[files]]", StringComparison.Ordinal);
        Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(text.Remove(start, end - start)));
        var duplicate = "[evidence.artifact_kinds.JSON]\nprofile = \"structured-json\"\nselectors = [\"result\"]\npath_selectors = [\"formal\"]\n\n";
        Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(text.Insert(end, duplicate)));
    }

    [Theory]
    [InlineData("pattern = \"README.md\"", "pattern = \"Readme.md\"")]
    [InlineData("selectors = [\"source\"]", "selectors = [\"input\", \"source\"]")]
    [InlineData("path_selectors = [\"formal\", \"kernels\"]", "path_selectors = [\"formal\"]")]
    [InlineData("profile = \"structured-json\"", "profile = \"opaque-text\"")]
    [InlineData("digestion_source = true", "")]
    [InlineData("admission_plane = \"judge\"", "admission_plane = \"content\"")]
    [InlineData("consumed_by = [\"reader\"]", "consumed_by = [\"agent\"]")]
    public void PolicyIdentityIncludesEveryAuthorityDimension(string before, string after)
    {
        Assert.Contains(before, TestFileMap.Canonical, StringComparison.Ordinal);
        var original = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        var changed = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical.Replace(before, after, StringComparison.Ordinal))).Policy;
        Assert.NotEqual(original.FileMapSha256, changed.FileMapSha256);
    }

    [Fact]
    public void MembershipDoesNotBypassCanonicalCoordinatesAndAmbiguityFailsClosed()
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("surprise.json"), policy));
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("Evidence/D5/Bad.json"), policy));
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes(TestFileMap.Canonical), "test");
        var extra = FileMapLoader.Parse(Encoding.UTF8.GetBytes(TestFileMap.Canonical.Replace("pattern = \"Evidence/**\"", "pattern = \"Evidence/D5/**\"", StringComparison.Ordinal)), "test").Entries.Single(e => e.Pattern == "Evidence/D5/**");
        var ambiguous = new FileMapManifest(manifest.ResidencePolicy, manifest.Entries.Add(extra).OrderBy(e => e.Pattern, StringComparer.Ordinal).ToImmutableArray(), manifest.ArtifactKinds);
        var ambiguousPolicy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(FileMapCanonicalWriter.Write(ambiguous).AsSpan(), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        Assert.Contains("matches=2", RepositoryPathPolicy.Validate(RepoPath.CreateKnown("Evidence/D5/S0/Carrier/Demo.result.json"), ambiguousPolicy)!.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(true, true, false)]
    [InlineData(false, true, true)]
    [InlineData(false, false, false)]
    public void FileMapEligibilityChangesRecheckUnchangedSourceMetadata(
        bool eligible, bool policyChanged, bool rejected)
    {
        const string path = "docs/GOVERNANCE.md";
        var fileMap = eligible ? TestFileMap.Canonical : TestFileMap.Canonical.Replace(
            "digestion_source = true\n", string.Empty, StringComparison.Ordinal);
        var policy = PolicyLoadAssert.Accepted(Load(fileMap)).Policy;
        var current = Snapshot(fileMap);
        var baseline = Snapshot(TestFileMap.Canonical);
        var changes = RawChangeSet.Create([policyChanged ? "Meta/FILEMAP.toml" : "README.md"]);
        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(current, baseline, policy, null, changes),
            DigestionTestSupport.Document(AtomizerRegistry.NoAtomizerId, [], sourcePath: path));

        Assert.Equal(eligible, policy.IsDigestionSource(RepoPath.CreateKnown(path)));
        Assert.False(policy.IsDigestionSource(RepoPath.CreateKnown("README.md")));
        Assert.Equal(rejected, findings.Any(finding => finding.Message.Contains(
            "declare digestion_source = true", StringComparison.Ordinal)));

        static RepositorySnapshot Snapshot(string manifest) =>
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            [
                RawRepositoryEntry.FromText(path, "# Governance\n"),
                RawRepositoryEntry.FromText("Meta/FILEMAP.toml", manifest),
            ]))).Snapshot;
    }

    [Theory]
    [InlineData("domains:", "domains: &v", "anchor")]
    [InlineData("domains:", "domains: *v", "alias")]
    [InlineData("domains:", "domains: !custom", "tag")]
    [InlineData("domains:", "domains:\n  <<: {}", "merge")]
    [InlineData("stratum: S0", "stratum: S8", "Invalid domain")]
    [InlineData("stratum: S0", "stratum: 0", "Invalid domain")]
    [InlineData("stratum: S0", "stratum: 100", "Invalid domain")]
    [InlineData("  Conventions:", "  carrier:", "domain")]
    [InlineData("  Conventions:", "  Carrier:", "Duplicate")]
    public void DomainVocabularyRetainsStrictYamlValidation(string before, string after, string marker)
    {
        var failure = Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(TestFileMap.Canonical, TestFileMap.Domains.Replace(before, after, StringComparison.Ordinal)));
        Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
    }
}
