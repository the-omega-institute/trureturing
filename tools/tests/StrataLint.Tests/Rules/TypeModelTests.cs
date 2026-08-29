using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TypeModelTests
{
    [Theory]
    [InlineData("Blueprint/Trureturing.Content.csproj")]
    [InlineData("Blueprint/Another.Content.csproj")]
    [InlineData("Blueprint/trureturing.content.csproj")]
    [InlineData("Blueprint/Program.cs")]
    [InlineData("Blueprint/packages.lock.json")]
    public void BlueprintContentCompositionBuildFilesAreClosedWorldRegistered(string value)
    {
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Theory]
    [InlineData("Blueprint/D5/Foo.csproj")]
    [InlineData("Blueprint/random.txt")]
    [InlineData("Blueprint/sub/x.csproj")]
    [InlineData("Blueprint/Trureturing.Content.sln")]
    [InlineData("Blueprint/Trureturing.Content.slnx")]
    [InlineData("Blueprint/D5/Trureturing.Content.csproj")]
    [InlineData("Blueprint/FOO.CSPROJ")]
    [InlineData("Blueprint/Foo.csproj.bak")]
    [InlineData("Blueprint/.csproj")]
    [InlineData("Blueprint/Directory.Build.props")]
    [InlineData("Blueprint/Directory.Build.targets")]
    [InlineData("Blueprint/NuGet.Config")]
    [InlineData("Blueprint/.editorconfig")]
    [InlineData("Blueprint/Main.cs")]
    public void BlueprintContentCompositionBuildFileNeighborsRemainSl000Blocked(string value)
    {
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, Policy()));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(value, issue.Path);
        Assert.Equal(
            "noncanonical Blueprint artifact: path is not a canonical semantic artifact",
            issue.Message);
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Fact]
    public void BlueprintCompositionRootAllowsOnlyOneDirectProject()
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                RawRepositoryEntry.FromText("Blueprint/One.csproj", "<Project />\n"),
                RawRepositoryEntry.FromText("Blueprint/Two.csproj", "<Project />\n"),
            ]))).Snapshot;

        var descriptor = new RuleDescriptor(
            RuleId.CreateKnown(15),
            "test",
            DisplaySeverity.Error,
            "test",
            AdmissionEffect.Observe,
            RuleLifecycle.Active,
            null);
        var finding = Assert.Single(RepositoryPathPolicy.Evaluate(snapshot, Policy(), descriptor));

        Assert.Equal("Blueprint/Two.csproj", finding.Path);
        Assert.Equal("Blueprint composition root allows at most one direct .csproj", finding.Message);
    }

    [Fact]
    public void BlueprintCompositionRootUsesOrdinalExtensionAndRejectsDirectoryShape()
    {
        Assert.True(RepositoryPathPolicy.IsBlueprintContentCompositionBuildFile(
            "Blueprint/trureturing.content.csproj"));
        Assert.False(RepositoryPathPolicy.IsBlueprintContentCompositionBuildFile(
            "Blueprint/D5/Future.Content.csproj"));
        Assert.False(RepositoryPathPolicy.IsBlueprintContentCompositionBuildFile(
            "Blueprint/FOO.CSPROJ"));
        var exception = Assert.Throws<ArgumentException>(
            () => RepoPath.CreateKnown("Blueprint/Trureturing.Content.csproj/"));
        Assert.Equal("Invalid repository path. (Parameter 'value')", exception.Message);
    }

    [Theory]
    [InlineData("Generated/echo-residuals/source-a.md", true)]
    [InlineData("Generated/echo-residuals/a/b.md", false)]
    [InlineData("Generated/echo-residuals/a.txt", false)]
    [InlineData("Generated/echo-residuals/.md", false)]
    [InlineData("Generated/echo-residualsX/a.md", false)]
    public void EchoResidualShardPathPredicateIsClosed(string value, bool expected)
    {
        Assert.Equal(expected, RepositoryPathPolicy.IsEchoResidualShardPath(value));
    }

    [Fact]
    public void ProblemPoolCandidateIsClosedWorldRegisteredButNotASemanticTarget()
    {
        var path = RepoPath.CreateKnown("Problems/wall-sun-sun-golden-unit-lift.md");

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    // The one-problem-one-file partition of spec 11.20.3 has no guard of its own:
    // a nested path, a non-Markdown payload and an uppercase stem are rejected only
    // because the canonical path predicate does not match them, so the SL-000
    // direction is pinned here rather than left to the committed files.
    [Theory]
    [InlineData("Problems/sub/x.md")]
    [InlineData("Problems/index.json")]
    [InlineData("Problems/Foo.md")]
    [InlineData("Problems/wall-sun-sun.md.bak")]
    [InlineData("Problems/.md")]
    [InlineData("ProblemsX/a.md")]
    public void ProblemPoolPathGrammarRejectsNoncanonicalNeighbors(string value)
    {
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, Policy()));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(value, issue.Path);
        Assert.Equal("unknown top-level artifact", issue.Message);
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    private const string PaperRecipePath = "Papers/recipes/D5-P001.yaml";

    [Fact]
    public void DigestionCasBlobIsClosedWorldRegisteredButNotASemanticTarget()
    {
        var path = RepoPath.CreateKnown(
            DigestionCasStore.RootPath + new string('a', 64));

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Theory]
    [InlineData("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")]
    [InlineData("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa/extra")]
    public void DigestionCasPathGrammarRejectsNoncanonicalNeighbors(string relative)
    {
        var value = DigestionCasStore.RootPath + relative;
        var path = RepoPath.CreateKnown(value);

        Assert.False(DigestionCasStore.IsCanonicalPath(value));
        Assert.NotNull(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    private const string RawDefinitionSourcePath = "Blueprint/D5/S1/Digit/Raw.scribe.cs";

    [Fact]
    public void GidRejectsUnsafeMachineCharacters()
    {
        Assert.False(Gid.TryParse("D5/S0/Carrier/Ring@bad", out _));
    }

    [Fact]
    public void RepoPathRejectsTraversalAndBackslashes()
    {
        Assert.False(RepoPath.TryCreate("../D5/S0/Carrier/Ring.lean", out _));
        Assert.False(RepoPath.TryCreate("D5\\S0\\Carrier\\Ring.lean", out _));
    }

    [Fact]
    public void RuleAndCaseIdsAreClosedByGrammar()
    {
        Assert.True(RuleId.TryCreate("SL-022", out _));
        Assert.True(RuleId.TryCreate("SL-023", out _));
        Assert.False(RuleId.TryCreate("SL-024", out _));
        Assert.True(RuleId.TryCreate("SL-025", out _));
        Assert.False(RuleId.TryCreate("SL-027", out _));
        Assert.True(RuleId.TryCreate("SL-028", out _));
        Assert.True(CaseId.TryCreate("D5-T0016", out _));
    }

    [Theory]
    [InlineData(23, true)]
    [InlineData(24, false)]
    [InlineData(25, true)]
    [InlineData(26, true)]
    [InlineData(27, false)]
    [InlineData(28, true)]
    [InlineData(29, false)]
    public void RuleIdKnownDomainPreservesTheIntentionalGapAndUpperBoundary(
        int number,
        bool expected)
    {
        if (expected)
        {
            Assert.Equal($"SL-{number:000}", RuleId.CreateKnown(number).Value);
            return;
        }

        Assert.Throws<ArgumentOutOfRangeException>(() => RuleId.CreateKnown(number));
    }

    [Fact]
    public void ValidationProfilesAreAClosedUnion()
    {
        ValidationProfile profile = new ValidationProfile.StructuredJson();
        Assert.Equal("structured-json", profile.Match(
            structuredJson: static _ => "structured-json",
            structuredYaml: static _ => "structured-yaml",
            leanModule: static _ => "lean-module",
            opaqueText: static _ => "opaque-text"));
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Ring", RuleFixture.RingPath)]
    [InlineData("D5/S0/Carrier/Algebra/Ring", "D5/S0/Carrier/Algebra/Ring.lean")]
    [InlineData("D5/S0/Carrier/Ring.norm_mul", RuleFixture.RingPath)]
    [InlineData("D5/B/S0/Carrier/Ring", RuleFixture.BlueprintPath)]
    [InlineData("D5/E/S0/Carrier/Ring.result--json", "Evidence/D5/S0/Carrier/Ring.result.json")]
    [InlineData("D5/E/values--json", RuleFixture.ValuesProjectionPath)]
    [InlineData("D5/E/values.result--json", "Evidence/D5/values.result.json")]
    [InlineData("D5/E/experiments/D5-X0001.spec--yaml", "Evidence/D5/experiments/D5-X0001.spec.yaml")]
    [InlineData("D5/C/2026-07-11/r168", "Chronicle/2026/07/11-r168.md")]
    [InlineData("D5/L/bellissard1992gap", "Library/notes/bellissard1992gap.md")]
    [InlineData("D5/L/Weil/sample2026paper", "Library/Weil/sample2026paper.md")]
    [InlineData("D5/P/D5-P001", PaperRecipePath)]
    [InlineData("D5/P/D5-P001--frozen", "Papers/frozen/D5-P001/manifest.sha256")]
    public void GidAndTargetAreCanonicalTwoWayMappings(string text, string path)
    {
        Assert.True(Gid.TryParse(text, out var gid));
        Assert.Equal(path, gid.Path.Value);

        var target = gid.ToTarget();
        var printed = Gid.FromTarget(target);

        Assert.Equal(gid, printed);
        Assert.Equal(target, printed.ToTarget());
        Assert.Equal(text, printed.Value);
    }

    [Fact]
    public void ThreeSegmentFormalGidRetainsItsExactBytes()
    {
        const string text = "D5/S0/Carrier/Probe";

        Assert.True(Gid.TryParse(text, out var gid));
        Assert.Equal(text, gid.Value);
        Assert.Equal("D5/S0/Carrier/Probe.lean", gid.Path.Value);
    }

    [Theory]
    [InlineData("D5/E/../Ring.result--json")]
    [InlineData("D5/E/./Ring.result--json")]
    [InlineData("D5/E/foo//Ring.result--json")]
    [InlineData("D5/E/S0/Carrier/Ring--json")]
    [InlineData("D5/B/S0/Carrier/Ring.declaration")]
    [InlineData("D5/L/NOTES/sample2026paper")]
    [InlineData("D5/L/Notes/sample2026paper")]
    [InlineData("D5/L/zeros/sample2026paper")]
    [InlineData("D5/L/Weil/sample2026paper/extra")]
    [InlineData("D8/S0/Carrier/Ring")]
    [InlineData("D5/S0/Carrier/Algebra/Extra/Ring")]
    [InlineData("D5/S0/Carrier/Carrier/Ring")]
    public void GidRejectsUnsafeOrNoncanonicalNeighbors(string text)
    {
        Assert.False(Gid.TryParse(text, out _));
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Algebra/Ring.lean", "D5/S0/Carrier/Algebra/Ring")]
    [InlineData("Evidence/D5/S0/Carrier/Algebra/Ring.result.json", "D5/E/S0/Carrier/Algebra/Ring.result--json")]
    public void RepositoryPathPolicyAdmitsFourCoordinateFormalScopeRoundTrips(string value, string expectedGid)
    {
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.True(RepositoryPathPolicy.TryResolve(path, Policy(), out var gid));
        Assert.NotNull(gid);
        Assert.Equal(expectedGid, gid.Value);
        Assert.Equal(path, gid.Path);
    }

    [Fact]
    public void RepositoryPathPolicyAdmitsFourCoordinateBlueprintDefinitionSource()
    {
        var path = RepoPath.CreateKnown("Blueprint/D5/S0/Carrier/Algebra/Ring.scribe.cs");

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, Policy(), out _));
    }

    [Fact]
    public void RepositoryPathPolicyRejectsFiveCoordinateFormalPathAsAddressShape()
    {
        var path = RepoPath.CreateKnown("D5/S0/Carrier/Algebra/Extra/Ring.lean");

        var issue = Assert.IsType<RepositoryPathIssue>(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(
            "noncanonical formal artifact: formal address must be Sn/Domain[/SubDomain]/Module or X_Zone/Module",
            issue.Message);
        Assert.False(RepositoryPathPolicy.TryResolve(path, Policy(), out _));
    }

    [Fact]
    public void RepositoryPathPolicyRejectsUncontrolledLibrarySplitBucket()
    {
        var path = RepoPath.CreateKnown("Library/Unknown/sample2026paper.md");

        Assert.NotNull(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, Policy(), out _));
    }

    [Fact]
    public void BlueprintDefinitionSourceIsContentButNotASecondSemanticTarget()
    {
        var path = RepoPath.CreateKnown(RawDefinitionSourcePath);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Fact]
    public void BlueprintDefinitionSourceStillObeysCanonicalAddressGrammar()
    {
        var path = RepoPath.CreateKnown("Blueprint/D5/S1/Digit/raw.scribe.cs");

        Assert.NotNull(RepositoryPathPolicy.Validate(path, Policy()));
    }

    [Theory]
    [InlineData("tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml")]
    [InlineData("Golden/Projection/x.json")]
    [InlineData("Golden/Frozen/accepted/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json")]
    [InlineData("Golden/values-kernels.toml")]
    public void CanonicalGoldenDataResidencesAreClosedWorldRegistered(string value)
    {
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Theory]
    [InlineData("Golden/other.toml")]
    [InlineData("Golden/EngineeringTestRetirements/example.json")]
    [InlineData("Golden/EngineeringTestRetirements/.json")]
    [InlineData("Golden/EngineeringTestRetirements/example.toml")]
    [InlineData("Golden/EngineeringTestRetirements/nested/example.json")]
    [InlineData("Golden/Other/x.json")]
    [InlineData("Golden/Projection/nested/x.json")]
    [InlineData("Golden/Projection/x.toml")]
    [InlineData("Golden/Projection/.json")]
    [InlineData("Golden/Projection/bad.name.json")]
    [InlineData("Golden/Projection/bad+name.json")]
    [InlineData("Golden/Projection/caf\u00e9.json")]
    [InlineData("Golden/Frozen/accepted/nested/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json")]
    [InlineData("Golden/Frozen/other/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json")]
    public void CanonicalGoldenDataResidencesRejectNoncanonicalNeighbors(string value)
    {
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, Policy()));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Fact]
    public void HarnessGateScriptIsClosedWorldRegisteredAndBootstrapProtected()
    {
        const string value = RuleFixture.HarnessGatePath;
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        var outcome = BootstrapGate.Evaluate(RawChangeSet.Create(new[] { value }));
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(outcome);
        Assert.Contains(verification.ChangeSet.Paths, item => item == path);
    }

    [Fact]
    public void MakefileIsClosedWorldRegisteredAndBootstrapProtected()
    {
        const string value = "Makefile";
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        var outcome = BootstrapGate.Evaluate(RawChangeSet.Create([value]));
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(outcome);
        Assert.Contains(verification.ChangeSet.Paths, item => item == path);
    }

    [Fact]
    public void FileMapDataIsGovernanceRegisteredAndBootstrapClear()
    {
        const string value = "Meta/FILEMAP.toml";
        var path = RepoPath.CreateKnown(value);
        var policy = Policy();

        Assert.Contains(path, policy.GovernanceDocuments);
        Assert.Null(RepositoryPathPolicy.Validate(path, policy));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
        Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([value])));
    }

    private static ValidatedPolicy Policy() =>
        RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
}
