using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class RepositoryPolicyRegressionAssertions
{
    private static PolicyLoadOutcome Load(string fileMap, string? domains = null) => RepositoryPolicyLoader.Load(
        Encoding.UTF8.GetBytes(fileMap), Encoding.UTF8.GetBytes(domains ?? TestFileMap.Domains));

    internal static void Run()
    {
        foreach (var (registeredPath, pattern, path) in new[]
        {
            ("global.json", "global.*", "global.json"),
            ("global.json", "global.*", "global.txt"),
            ("agents/adversary.md", "agents/adversary.*", "agents/adversary.md"),
            ("agents/adversary.md", "agents/adversary.*", "agents/adversary.txt"),
        })
            RootAndAgentCharterGlobsAreRejected(registeredPath, pattern, path);
        foreach (var (registeredPath, widerPath) in new[]
        {
            ("global.json", "global.txt"),
            ("agents/adversary.md", "agents/adversary.txt"),
        })
            RootAndAgentCharterExactEntriesRemainRequired(registeredPath, widerPath);
        foreach (var (tomlValue, expected) in new[]
        {
            ("😀", "😀"),
            ("\\U0001F600", "😀"),
            ("\\U00010000\\U0010FFFF", "\U00010000\U0010FFFF"),
            ("中é\\u0000\\u0001\\b\\t\\n\\f\\r\\u007F\\\"\\\\end", "中é\0\u0001\b\t\n\f\r\u007F\"\\end"),
        })
            AcceptedUnicodeScalarsHaveCanonicalTomlRoundTrips(tomlValue, expected);
        UnicodeDirectoryLinksRoundTripInTheirOwnSnapshot();
        foreach (var (kind, selector, profile) in new[]
        {
            ("csv", "result", "opaque-text"),
            ("json", "run", "structured-json"),
            ("md", "result", "opaque-text"),
            ("py", "source", "opaque-text"),
            ("txt", "result", "opaque-text"),
            ("yaml", "spec", "structured-yaml"),
            ("yml", "spec", "structured-yaml"),
        })
            EveryEvidenceFormatRoutesAndDecodesThroughFileMap(kind, selector, profile);
        foreach (var (kind, coordinate, selector, allowed) in new (string, string, string, bool)[]
        {
            ("csv", "experiments/D5-X0001", "result", false),
            ("json", "experiments/D5-X0001", "run", true),
            ("json", "kernels/Demo", "check", true),
            ("json", "X_Frontier/Demo", "quote", true),
            ("md", "X_Frontier/Demo", "result", true),
            ("py", "kernels/Demo", "source", true),
            ("txt", "kernels/Demo", "result", false),
            ("yaml", "experiments/D5-X0001", "spec", true),
            ("yml", "experiments/D5-X0001", "run", true),
            ("json", "S0/Carrier/Demo", "source", false),
            ("json", "S1/Carrier/Demo", "result", false),
            ("json", "S0/Unknown/Demo", "result", false),
        })
            EvidenceSelectorsScopesAndDomainsAreConjunctive(kind, coordinate, selector, allowed);
        AssertPolicyIdentityIncludesEveryAuthorityDimension();
        MembershipDoesNotBypassCanonicalCoordinatesAndAmbiguityFailsClosed();
        FileMapEligibilityChangesRecheckUnchangedSourceMetadata(true, true, false);
        FileMapEligibilityChangesRecheckUnchangedSourceMetadata(false, true, true);
        FileMapEligibilityChangesRecheckUnchangedSourceMetadata(false, false, false);
        foreach (var (before, after, marker) in new[]
        {
            ("domains:", "domains: &v", "anchor"),
            ("domains:", "domains: *v", "alias"),
            ("domains:", "domains: !custom", "tag"),
            ("domains:", "domains:\n  <<: {}", "merge"),
            ("stratum: S0", "stratum: S8", "Invalid domain"),
            ("stratum: S0", "stratum: 0", "Invalid domain"),
            ("stratum: S0", "stratum: 100", "Invalid domain"),
            ("  Conventions:", "  carrier:", "domain"),
            ("  Conventions:", "  Carrier:", "Duplicate"),
        })
            DomainVocabularyRetainsStrictYamlValidation(before, after, marker);
    }

    private static void RootAndAgentCharterGlobsAreRejected(string registeredPath, string pattern, string path)
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical.Replace(
            $"pattern = \"{registeredPath}\"", $"pattern = \"{pattern}\"", StringComparison.Ordinal))).Policy;
        Assert.Equal(pattern, Assert.Single(policy.Manifest.Match(path)).Pattern);
        Assert.Empty(FileMapPolicy.InspectCoverage(policy.Manifest, [path]));
        Assert.DoesNotContain(FileMapPolicy.InspectPatternPopulation(policy.Manifest, [path]),
            finding => finding.Path == pattern);

        var issue = Assert.IsType<RepositoryPathIssue>(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(path, issue.Path);
        Assert.Equal("root files and agent charters require an exact FILEMAP entry", issue.Message);
    }

    private static void RootAndAgentCharterExactEntriesRemainRequired(string registeredPath, string widerPath)
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        Assert.Equal(registeredPath, Assert.Single(policy.Manifest.Match(registeredPath)).Pattern);
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(registeredPath), policy));
        var issue = Assert.IsType<RepositoryPathIssue>(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(widerPath), policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Contains("matches=0", issue.Message, StringComparison.Ordinal);

        // FILEMAP alone supplies membership, including a newly registered literal name.
        var widerPolicy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical.Replace(
            $"pattern = \"{registeredPath}\"", $"pattern = \"{widerPath}\"", StringComparison.Ordinal))).Policy;
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(widerPath), widerPolicy));
    }

    private static void AcceptedUnicodeScalarsHaveCanonicalTomlRoundTrips(string tomlValue, string expected)
    {
        var source = TestFileMap.Canonical.Replace("data-must-live-outside-tools", tomlValue, StringComparison.Ordinal);
        var first = PolicyLoadAssert.Accepted(Load(source)).Policy;
        Assert.Equal(expected, first.Manifest.ResidencePolicy.Desired);
        var second = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            first.CanonicalFileMapBytes.AsSpan(), first.CanonicalDomainsBytes.AsSpan())).Policy;

        Assert.Equal(expected, second.Manifest.ResidencePolicy.Desired);
        Assert.Equal(first.CanonicalFileMapBytes.ToArray(), second.CanonicalFileMapBytes.ToArray());
        Assert.Equal(first.FileMapSha256, second.FileMapSha256);
        if (!expected.Any(char.IsControl))
        {
            var literal = PolicyLoadAssert.Accepted(Load(source.Replace(tomlValue, expected, StringComparison.Ordinal))).Policy;
            Assert.Equal(first.FileMapSha256, literal.FileMapSha256);
        }
    }

    private static void UnicodeDirectoryLinksRoundTripInTheirOwnSnapshot()
    {
        const string linkEntries = """
            [[files]]
            pattern = ".claude/skills"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["reader"]
            verified_by = ["repository-policy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            symlink = { target = "../skills", kind = "directory" }

            [[files]]
            pattern = ".codex/skills"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["reader"]
            verified_by = ["repository-policy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            symlink = { target = "../skills", kind = "directory" }
            """;
        var firstEntry = TestFileMap.Canonical.IndexOf("[[files]]", StringComparison.Ordinal);
        var source = TestFileMap.Canonical.Insert(firstEntry, linkEntries + "\n\n");
        const string original = "target = \"../skills\"";
        Assert.Equal(2, source.Split(original, StringSplitOptions.None).Length - 1);
        var modified = source.Replace(original, "target = \"../skills/😀\"", StringComparison.Ordinal);
        Assert.NotEqual(source, modified);
        var policy = PolicyLoadAssert.Accepted(Load(modified)).Policy;
        var originalEntries = Entries(Encoding.UTF8.GetBytes(modified));
        HashSet<string> links = [".claude/skills", ".codex/skills"];
        var paths = originalEntries.Select(entry => entry.Path).ToArray();
        FileMapSymlinkPolicy.ValidateSnapshot(originalEntries, links, paths);

        var reloaded = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            policy.CanonicalFileMapBytes.AsSpan(), policy.CanonicalDomainsBytes.AsSpan())).Policy;
        Assert.Equal(policy.FileMapSha256, reloaded.FileMapSha256);
        Assert.Equal(policy.CanonicalFileMapBytes.ToArray(), reloaded.CanonicalFileMapBytes.ToArray());
        var canonicalEntries = Entries(policy.CanonicalFileMapBytes);
        FileMapSymlinkPolicy.ValidateSnapshot(canonicalEntries, links, paths);
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(canonicalEntries))).Snapshot;
        Assert.IsType<CanonicalizationOutcome.Accepted>(RepositoryCanonicalizer.Validate(decoded, reloaded));
        Assert.Throws<InvalidOperationException>(() => FileMapSymlinkPolicy.ValidateSnapshot(
            canonicalEntries.Where(entry => entry.Path != "skills/😀/probe.md").ToArray(), links, paths));
        Assert.Throws<InvalidOperationException>(() => FileMapSymlinkPolicy.ValidateSnapshot(
            canonicalEntries.Select(entry => entry.Path == ".codex/skills"
                ? RawRepositoryEntry.FromText(entry.Path, "../skills") : entry).ToArray(), links, paths));

        RawRepositoryEntry[] Entries(IEnumerable<byte> fileMap) =>
        [
            new("Meta/FILEMAP.toml", fileMap.ToImmutableArray()),
            new("Meta/domains.yaml", policy.CanonicalDomainsBytes),
            RawRepositoryEntry.FromText(".claude/skills", "../skills/😀"),
            RawRepositoryEntry.FromText(".codex/skills", "../skills/😀"),
            RawRepositoryEntry.FromText("skills/😀/probe.md", "# Probe\n"),
        ];
    }

    private static void EveryEvidenceFormatRoutesAndDecodesThroughFileMap(string kind, string selector, string profile)
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

    private static void EvidenceSelectorsScopesAndDomainsAreConjunctive(string kind, string coordinate, string selector, bool allowed)
    {
        var policy = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
        var issue = RepositoryPathPolicy.Validate(RepoPath.CreateKnown($"Evidence/D5/{coordinate}.{selector}.{kind}"), policy);
        Assert.Equal(allowed, issue is null);
    }

    private static void AssertMissingEvidenceAndCaseCollidingKindsFailClosed()
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

        (string Before, string After, string Marker)[] malformed =
        [
            ("schema_version = 3", "schema_version = 2", "schema_version"),
            ("schema_version = 3", "schema_version = 3\nunknown = true", "unknown"),
            ("schema_version = 3", "schema_version = 3\nschema_version = 3", "TOML"),
            ("profile = \"structured-json\"", "profile = \"structured-json\"\nprofile = \"opaque-text\"", "TOML"),
            ("profile = \"structured-json\"", "profile = \"unknown\"", "profile"),
            ("profile = \"structured-json\"", "profile = 1", "profile"),
            ("profile = \"structured-json\"", "", "missing"),
            ("selectors = [\"source\"]", "selectors = []", "selectors"),
            ("selectors = [\"source\"]", "selectors = [\"source\", \"Source\"]", "case-colliding"),
            ("selectors = [\"source\"]", "selectors = [\"source\", \"source\"]", "duplicate"),
            ("selectors = [\"source\"]", "selectors = [\"../source\"]", "invalid"),
            ("path_selectors = [\"formal\", \"kernels\"]", "path_selectors = [\"unknown\"]", "path_selectors"),
            ("digestion_source = true", "digestion_source = false", "digestion_source"),
        ];
        foreach (var (before, after, marker) in malformed)
        {
            Assert.Contains(before, TestFileMap.Canonical, StringComparison.Ordinal);
            var failure = Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(
                Load(TestFileMap.Canonical.Replace(before, after, StringComparison.Ordinal)));
            Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
            var thrown = Assert.ThrowsAny<Exception>(() => PolicyLoadAssert.Accepted(failure));
            Assert.Contains(marker, thrown.Message, StringComparison.OrdinalIgnoreCase);
        }

        var text = TestFileMap.Canonical;
        var start = text.IndexOf("[evidence.", StringComparison.Ordinal);
        var end = text.IndexOf("[[files]]", StringComparison.Ordinal);
        Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(text.Remove(start, end - start)));
        var duplicate = "[evidence.artifact_kinds.JSON]\nprofile = \"structured-json\"\nselectors = [\"result\"]\npath_selectors = [\"formal\"]\n\n";
        Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(text.Insert(end, duplicate)));
    }

    private static void AssertPolicyIdentityIncludesEveryAuthorityDimension()
    {
        AssertMissingEvidenceAndCaseCollidingKindsFailClosed();
        (string Before, string After)[] changes =
        [
            ("pattern = \"README.md\"", "pattern = \"Readme.md\""),
            ("selectors = [\"source\"]", "selectors = [\"input\", \"source\"]"),
            ("path_selectors = [\"formal\", \"kernels\"]", "path_selectors = [\"formal\"]"),
            ("profile = \"structured-json\"", "profile = \"opaque-text\""),
            ("digestion_source = true", ""),
            ("admission_plane = \"judge\"", "admission_plane = \"content\""),
            ("consumed_by = [\"reader\"]", "consumed_by = [\"agent\"]"),
        ];
        foreach (var (before, after) in changes)
        {
            Assert.Contains(before, TestFileMap.Canonical, StringComparison.Ordinal);
            var original = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical)).Policy;
            var changed = PolicyLoadAssert.Accepted(Load(TestFileMap.Canonical.Replace(before, after, StringComparison.Ordinal))).Policy;
            Assert.NotEqual(original.FileMapSha256, changed.FileMapSha256);
        }
    }

    private static void MembershipDoesNotBypassCanonicalCoordinatesAndAmbiguityFailsClosed()
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

    private static void FileMapEligibilityChangesRecheckUnchangedSourceMetadata(
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

    private static void DomainVocabularyRetainsStrictYamlValidation(string before, string after, string marker)
    {
        var failure = Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(Load(TestFileMap.Canonical, TestFileMap.Domains.Replace(before, after, StringComparison.Ordinal)));
        Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
    }
}
