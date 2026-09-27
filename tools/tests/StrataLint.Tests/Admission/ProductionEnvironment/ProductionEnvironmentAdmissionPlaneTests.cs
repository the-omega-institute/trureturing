using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string FileMapPath = "Meta/FILEMAP.toml";
    private const string OrdinaryJudgePath = "LICENSE";
    private static readonly string DefaultAdmissionPlaneFileMap = CreateDefaultAdmissionPlaneFileMap();

    [Theory]
    [InlineData("ordinary", 0)]
    [InlineData("protected", 3)]
    [InlineData("blocked", 1)]
    [InlineData("infrastructure", 2)]
    [InlineData("single-plane", 0)]
    public void CandidateCheckPreservesMixedWarningAndOrdinaryValidation(string scenario, int expectedExit)
    {
        var fixture = TrustedFrozenFixture();
        if (scenario == "blocked") fixture.Apply("upward-import");
        fixture.Files[OrdinaryJudgePath] = "fixture license\n";
        fixture.Baseline[OrdinaryJudgePath] = fixture.Files[OrdinaryJudgePath];
        InstallAdmissionPlaneFileMap(fixture);
        var changes = RawChangeSet.Create(scenario == "single-plane"
            ? [RuleFixture.BlueprintPath]
            : [scenario == "protected" ? RuleFixture.SyntheticProtectedPath : OrdinaryJudgePath,
                RuleFixture.BlueprintPath, RuleFixture.RingPath]);
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));
        using var temporary = new TemporaryDirectory();
        var report = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(report, Decode(Snapshot(fixture.Files)), LeanAxiomReport.Create(fixture.Reports));
        if (scenario == "infrastructure") File.WriteAllText(report, "invalid JSON");
        string[] arguments = ["--candidate-lean-report", report];

        var outcome = environment.Check(arguments);
        var observations = outcome switch
        {
            AdmissionOutcome.Admitted admitted => admitted.Observations,
            AdmissionOutcome.ProtectedSurfaceChange change => change.Observations,
            AdmissionOutcome.RuleRejected rejected => rejected.Diagnostics,
            AdmissionOutcome.InfrastructureFailure failure => failure.Observations,
            _ => throw new InvalidOperationException("unexpected check outcome"),
        };
        if (scenario == "single-plane")
            Assert.DoesNotContain(observations, item => item.RuleId == RuleId.CreateKnown(29));
        else AssertAdmissionPlaneWarning(observations);
        if (scenario is "ordinary" or "single-plane")
            AssertCompleteRuleDisposition(Assert.IsType<AdmissionOutcome.Admitted>(outcome).Certificate);
        if (scenario == "protected")
            AssertCompleteRuleDisposition(Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome).ContentCertificate);
        if (scenario == "blocked")
            Assert.Contains(Assert.IsType<AdmissionOutcome.RuleRejected>(outcome).Diagnostics,
                item => item.RuleId == RuleId.CreateKnown(1) && item.AdmissionEffect == AdmissionEffect.Block);
        if (scenario == "infrastructure") Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);

        var console = new BufferedConsole();
        Assert.Equal(expectedExit, CliApplication.Run(["check", .. arguments], environment, console));
        Assert.Equal(scenario == "single-plane" ? 0 : 1,
            console.Output.Split("ADMISSION-PLANE-MIXED", StringSplitOptions.None).Length - 1);
        if (scenario == "blocked") Assert.Contains("SL-001", console.Output, StringComparison.Ordinal);
    }

    private static void AssertAdmissionPlaneWarning(ImmutableArray<Diagnostic> diagnostics)
    {
        var diagnostic = Assert.Single(diagnostics, item => item.RuleId == RuleId.CreateKnown(29));
        Assert.Equal("Admission plane partition", diagnostic.Title);
        Assert.Equal(DisplaySeverity.Warning, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.StartsWith("ADMISSION-PLANE-MIXED:", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("judge")]
    [InlineData("content")]
    public void CandidateCheckClassifiesDeletedFileAfterRegistrationRemoval(string deletedPlane)
    {
        const string deletedPath = "retired/component.txt";
        var fixture = TrustedFrozenFixture();
        fixture.Baseline[deletedPath] = "retired component\n";
        fixture.Baseline[FileMapPath] = Manifest(fixture.Baseline.Keys.Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .Select(path => (path, Plane: (string?)(path == FileMapPath ? "judge"
                : path == deletedPath ? deletedPlane : "content"))).ToArray());
        fixture.Files[FileMapPath] = CurrentManifest(fixture.Files.Keys.Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .Select(static path => (path, Plane: (string?)(path == FileMapPath ? "judge" : "content")))
            .ToArray());
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds(
                [
                    (FileMapPath, RawChangeKind.Modified),
                    (deletedPath, RawChangeKind.Deleted),
                ]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
        AssertCompleteRuleDisposition(protectedChange.ContentCertificate);
        if (deletedPlane == "content") AssertAdmissionPlaneWarning(protectedChange.Observations);
        else Assert.DoesNotContain(protectedChange.Observations, item => item.RuleId == RuleId.CreateKnown(29));
    }

    [Fact]
    public void AdmissionPlaneClassifiesNewJudgeFamilyFromCandidateFileMapInSameDelta()
    {
        const string newPath = "tools/new-lib/Program.cs";
        var fixture = TrustedFrozenFixture();
        InstallCandidateFileMapDelta(fixture, newPath, includeNewPath: true);
        var changes = RawChangeSet.Create([FileMapPath, newPath]);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var decision = AdmissionPlanePolicy.Evaluate(
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline, addDefaultFileMap: false),
            changes);
        var outcome = CheckWithReports(environment, fixture);

        Assert.True(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.JudgeOnly, decision.Classification);
        Assert.IsNotType<AdmissionOutcome.InfrastructureFailure>(outcome);
        if (outcome is AdmissionOutcome.RuleRejected rejected)
        {
            Assert.DoesNotContain(rejected.Diagnostics, static item =>
                item.RuleId == RuleId.CreateKnown(29));
        }
    }

    [Fact]
    public void AdmissionPlaneFailsClosedWhenCandidateFileMapLacksEntryForNewPath()
    {
        const string newPath = "tools/new-lib/Program.cs";
        var fixture = TrustedFrozenFixture();
        InstallCandidateFileMapDelta(fixture, newPath, includeNewPath: false);
        var changes = RawChangeSet.Create([FileMapPath, newPath]);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var decision = AdmissionPlanePolicy.Evaluate(
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline, addDefaultFileMap: false),
            changes);
        var outcome = CheckWithReports(environment, fixture);

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-PATH-MATCH-COUNT", decision.Code);
        Assert.Equal(newPath, decision.Path);
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(
            $"changed path must match exactly one FILEMAP entry; path={newPath} matches=0",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false, "judge")]
    [InlineData(true, "judge")]
    [InlineData(false, "content")]
    [InlineData(true, "content")]
    public void CandidateCheckUsesProtectedBaseForRetiredRegistration(bool rename, string oldPlane)
    {
        const string retired = "Meta/retired.toml";
        const string replacement = "Meta/replacement.toml";
        var fixture = TrustedFrozenFixture();
        fixture.Baseline[retired] = "retired configuration\n";
        fixture.Baseline[FileMapPath] = CurrentManifest(fixture.Baseline.Keys.Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .Select(path => (path, (string?)(path == retired ? oldPlane : path == FileMapPath ? "judge" : "content")))
            .ToArray());
        if (rename)
            fixture.Files[replacement] = fixture.Baseline[retired];
        fixture.Files[FileMapPath] = CurrentManifest(fixture.Files.Keys.Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .Select(path => (path, (string?)(path is FileMapPath or replacement ? "judge" : "content")))
            .ToArray());
        var changes = RawChangeSet.CreateWithKinds(
        [
            (FileMapPath, RawChangeKind.Modified),
            (retired, RawChangeKind.Deleted),
            .. rename ? new[] { (replacement, RawChangeKind.Added) } : [],
        ]);
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
        AssertCompleteRuleDisposition(protectedChange.ContentCertificate);
        var diagnostics = protectedChange.Observations;
        if (oldPlane == "content") AssertAdmissionPlaneWarning(diagnostics);
        else Assert.DoesNotContain(diagnostics, item => item.RuleId == RuleId.CreateKnown(29));
    }

    [Theory]
    [InlineData("missing", "FILEMAP is unavailable")]
    [InlineData("malformed", "FILEMAP cannot be parsed")]
    [InlineData("ambiguous", "matches=2")]
    [InlineData("unsafe", "FILEMAP-PATTERN-UNSAFE")]
    [InlineData("policy-content", "policy source must be assigned to the judge")]
    [InlineData("base-missing", "protected-base FILEMAP is unavailable")]
    [InlineData("base-malformed", "protected-base FILEMAP cannot be parsed")]
    [InlineData("base-ambiguous", "matches=2")]
    [InlineData("base-unregistered", "matches=0")]
    public void MixedCandidateCheckKeepsInvalidMetadataAsInfrastructureFailure(string defect, string message)
    {
        const string deleted = "retired/content.md";
        var fixture = TrustedFrozenFixture();
        fixture.Baseline[deleted] = "old content\n";
        InstallAdmissionPlaneFileMap(fixture);
        var baselineDefect = defect.StartsWith("base-", StringComparison.Ordinal);
        var files = baselineDefect ? fixture.Baseline : fixture.Files;
        var path = baselineDefect ? deleted : RuleFixture.BlueprintPath;
        switch (defect)
        {
            case "missing": case "base-missing": files.Remove(FileMapPath); break;
            case "malformed": case "base-malformed": files[FileMapPath] = "files = ["; break;
            case "ambiguous": case "base-ambiguous":
                files[FileMapPath] += $"\n[[files]]\npattern = '{path}'\nadmission_plane = 'content'\n"; break;
            case "unsafe": files[FileMapPath] += "\n[[files]]\npattern = 'unsafe/?.md'\nadmission_plane = 'content'\n"; break;
            case "policy-content": files[FileMapPath] = Manifest(("**", "content")); break;
            case "base-unregistered": files[FileMapPath] = Manifest((FileMapPath, "judge")); break;
        }
        var environment = new ProductionCliEnvironment("/repo", new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(FileMapPath, RawChangeKind.Modified),
                (RuleFixture.BlueprintPath, RawChangeKind.Modified), (deleted, RawChangeKind.Deleted)]),
            Snapshot(fixture.Files, addDefaultFileMap: false), Snapshot(fixture.Baseline, addDefaultFileMap: false)),
            new FakeLeanReportSource(null));
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(CheckWithReports(environment, fixture));
        Assert.Contains(message, failure.Message, StringComparison.Ordinal);
        Assert.Empty(failure.Observations);
    }

    [Fact]
    public void JudgeOnlyDeltaRemainsAdmissible()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "tools/change.cs");

        Assert.Null(outcome);
    }

    [Fact]
    public void ContentOnlyDeltaRemainsAdmissible()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "docs/change.md");

        Assert.Null(outcome);
    }

    [Fact]
    public void RealGitCopyClassifiesOnlyAddedDestination()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        TestGit.Run(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        var sourcePath = Path.Combine(repository.Path, "judge", "source.txt");
        var destinationPath = Path.Combine(repository.Path, "content", "copy.txt");
        var fileMapPath = Path.Combine(repository.Path, FileMapPath);
        Directory.CreateDirectory(Path.GetDirectoryName(sourcePath)!);
        Directory.CreateDirectory(Path.GetDirectoryName(destinationPath)!);
        Directory.CreateDirectory(Path.GetDirectoryName(fileMapPath)!);
        File.WriteAllText(sourcePath, "copy source\n", new UTF8Encoding(false));
        File.WriteAllText(
            fileMapPath,
            Manifest(("content/**", "content"), ("judge/**", "judge")),
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");
        var baseline = TestGit.Run(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();
        File.Copy(sourcePath, destinationPath);
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "candidate");
        var gateway = new GitRepositoryGateway(repository.Path);

        var prepared = gateway.Prepare(baseline);
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            gateway.ReadCurrent(),
            gateway.ReadRevision(prepared.Revision),
            prepared.Changes, out _);

        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "judge/source.txt" && change.Kind == RawChangeKind.Copied);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "content/copy.txt" && change.Kind == RawChangeKind.Added);
        Assert.Null(outcome);
    }

    [Fact]
    public void RenameDeleteAndAddSidesBothParticipateInClassification()
    {
        var changes = RawChangeSet.CreateWithKinds(
        [
            ("judge/source.txt", RawChangeKind.Deleted),
            ("content/destination.txt", RawChangeKind.Added),
        ]);

        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot(Encoding.UTF8.GetBytes(
                Manifest(("content/**", "content"), ("judge/**", "judge")))),
            AdmissionPlaneSnapshot(Encoding.UTF8.GetBytes(
                Manifest(("content/**", "content"), ("judge/**", "judge")))),
            changes, out var observations);

        Assert.Null(outcome);
        AssertAdmissionPlaneWarning(observations);
        Assert.Contains(observations, static item =>
            item.Message.Contains("ADMISSION-PLANE-MIXED", StringComparison.Ordinal));
    }

    [Fact]
    public void EmptyDeltaRemainsAdmissible()
    {
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot([0xff]),
            AdmissionPlaneSnapshot(null),
            RawChangeSet.Create([]), out _);

        Assert.Null(outcome);
    }

    [Fact]
    public void UnmatchedPathFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "content")),
            "tools/change.cs");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("path=tools/change.cs matches=0", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MultiplyMatchedPathFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "content"), ("docs/*.md", "content")),
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("path=docs/change.md matches=2", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAdmissionPlaneFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", null)),
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-ADMISSION-PLANE-MISSING", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void InvalidAdmissionPlaneFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "observer")),
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-ADMISSION-PLANE-INVALID", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void QuestionMarkPatternFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/?.md", "content")),
            "docs/a.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-PATTERN-UNSAFE", failure.Message, StringComparison.Ordinal);
        Assert.Contains("docs/?.md", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionPlaneFailsClosedWhenCandidateFileMapIsUnavailable()
    {
        var candidate = AdmissionPlaneSnapshot(null);
        var decision = AdmissionPlanePolicy.Evaluate(candidate, candidate, RawChangeSet.Create(["docs/change.md"]));
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            candidate,
            candidate,
            RawChangeSet.Create(["docs/change.md"]), out _);

        Assert.Equal("ADMISSION-PLANE-FILEMAP-UNAVAILABLE", decision.Code);
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP is unavailable", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("protected-base", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionPlaneFailsClosedWhenCandidateFileMapIsUnparseable()
    {
        var candidate = AdmissionPlaneSnapshot(Encoding.UTF8.GetBytes("files = [\n"));
        var decision = AdmissionPlanePolicy.Evaluate(candidate, candidate, RawChangeSet.Create(["docs/change.md"]));
        var outcome = EvaluateAdmissionPlane(
            "files = [\n",
            "docs/change.md");

        Assert.Equal("ADMISSION-PLANE-FILEMAP-INVALID", decision.Code);
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP cannot be parsed", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("protected-base", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionPlaneFailsClosedWhenCandidateFileMapIsNotUtf8()
    {
        var candidate = AdmissionPlaneSnapshot([0xff, 0xfe]);
        var decision = AdmissionPlanePolicy.Evaluate(candidate, candidate, RawChangeSet.Create([FileMapPath]));
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            candidate,
            candidate,
            RawChangeSet.Create([FileMapPath]), out _);

        Assert.Equal("ADMISSION-PLANE-FILEMAP-INVALID", decision.Code);
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("bytes are not strict UTF-8", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionPlaneAdmitsFirstFileMapIntroducedByCandidateWithNewJudgeFamily()
    {
        const string newPath = "tools/new-lib/Program.cs";
        var fixture = TrustedFrozenFixture();
        InstallCandidateFileMapDelta(
            fixture,
            newPath,
            includeNewPath: true,
            includeBaselineFileMap: false);
        var changes = RawChangeSet.Create([FileMapPath, newPath]);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline, addDefaultFileMap: false)),
            new FakeLeanReportSource(null));

        var decision = AdmissionPlanePolicy.Evaluate(
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline, addDefaultFileMap: false),
            changes);
        var outcome = CheckWithReports(environment, fixture);

        Assert.True(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.JudgeOnly, decision.Classification);
        Assert.IsNotType<AdmissionOutcome.InfrastructureFailure>(outcome);
        if (outcome is AdmissionOutcome.RuleRejected rejected)
        {
            Assert.DoesNotContain(rejected.Diagnostics, static item =>
                item.RuleId == RuleId.CreateKnown(29));
        }
    }

    [Fact]
    public void AdmissionPlaneRejectsLegacyRootSchemaForFlatAndIncludedFileMaps()
    {
        const string files = "files = [{ pattern = \"docs/**\", admission_plane = \"content\" }]\n";
        foreach (var manifest in new[]
        {
            "schema_version = 1\n" + files,
            "schema_version = 1\ninclude = [\"FILEMAP.inputs.toml\"]\n" + files,
        })
        {
            var outcome = EvaluateAdmissionPlane(manifest, "docs/change.md");

            var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
            Assert.Contains("root schema_version must be 2, 3, 4 or 5", failure.Message, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AdmissionPlaneRequiresRootSchemaBeforeClassifyingInlineFileArrays()
    {
        const string files = "files = [{ pattern = \"docs/**\", admission_plane = \"content\" }]\n";
        foreach (var manifest in new[]
        {
            files,
            "include = [\"FILEMAP.inputs.toml\"]\n" + files,
        })
        {
            var outcome = EvaluateAdmissionPlane(manifest, "docs/change.md");

            var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
            Assert.Contains("root schema_version must be 2, 3, 4 or 5", failure.Message, StringComparison.Ordinal);
        }

        Assert.Null(EvaluateAdmissionPlane("schema_version = 2\n" + files, "docs/change.md"));
        Assert.Null(EvaluateAdmissionPlane("schema_version = 3\n" + files, "docs/change.md"));
        Assert.Null(EvaluateAdmissionPlane("schema_version = 4\n" + files, "docs/change.md"));
        Assert.Null(EvaluateAdmissionPlane("schema_version = 5\n" + files, "docs/change.md"));
    }


    private static AdmissionOutcome? EvaluateAdmissionPlane(
        string manifest,
        params string[] changedPaths)
    {
        var snapshot = AdmissionPlaneSnapshot(Encoding.UTF8.GetBytes(manifest));
        return ProductionCliEnvironment.EvaluateAdmissionPlane(snapshot, snapshot, RawChangeSet.Create(changedPaths), out _);
    }

    private static RawRepositorySnapshot AdmissionPlaneSnapshot(byte[]? fileMapBytes) =>
        RawRepositorySnapshot.Create(fileMapBytes is null
            ? []
            : [new RawRepositoryEntry(FileMapPath, ImmutableArray.CreateRange(fileMapBytes))]);

    private static void InstallAdmissionPlaneFileMap(RuleFixture fixture)
    {
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
            files[FileMapPath] = CurrentManifest(files.Keys.Append(FileMapPath).Append(RuleFixture.SyntheticProtectedPath)
                .Distinct(StringComparer.Ordinal).Select(path => (path,
                    (string?)(path is FileMapPath or OrdinaryJudgePath
                        || path.StartsWith("tools/", StringComparison.Ordinal) ? "judge" : "content")))
                .ToArray());
    }

    private static void InstallCandidateFileMapDelta(
        RuleFixture fixture,
        string newPath,
        bool includeNewPath,
        bool includeBaselineFileMap = true)
    {
        const string project = "tools/new-lib/Fixture.csproj";
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[project] = "<Project />";
            files[EngineeringRegistrationFixture.Path] = EngineeringRegistrationFixture.Append(
                files[EngineeringRegistrationFixture.Path],
                new EngineeringProjectFixture(project, "Fixture", "test-support", false, ["tools/new-lib/**/*.cs"]));
        }
        var baselinePaths = fixture.Baseline.Keys
            .Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        if (includeBaselineFileMap)
        {
            fixture.Baseline[FileMapPath] = Manifest(baselinePaths
                .Select(static path => (
                    path,
                    Plane: (string?)(path == FileMapPath ? "judge" : "content")))
                .ToArray());
        }

        fixture.Files[newPath] = "internal sealed class Program { }\n";
        fixture.Files[FileMapPath] = CurrentManifest(baselinePaths
            .Concat(includeNewPath ? [newPath] : [])
            .Select(path => (
                path,
                Plane: (string?)(path is FileMapPath || path == newPath ? "judge" : "content")))
            .ToArray());
    }

    internal static void InstallDefaultAdmissionPlaneFileMap(RuleFixture fixture)
    {
        fixture.Files[FileMapPath] = DefaultAdmissionPlaneFileMap;
        fixture.Baseline[FileMapPath] = DefaultAdmissionPlaneFileMap;
    }

    private static string CreateDefaultAdmissionPlaneFileMap()
    {
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var entries = policy.Manifest.Entries.Select(entry => new FileMapEntry(
            entry.Pattern,
            entry.Kind,
            entry.Pattern == FileMapPath ? FileMapAdmissionPlane.Judge : FileMapAdmissionPlane.Content,
            entry.ProducedBy,
            entry.ConsumedBy,
            entry.VerifiedBy,
            entry.ResidenceViolation,
            entry.ArtifactId,
            entry.Mode,
            entry.RuntimeDisposition,
            entry.HistoryRequirement,
            entry.Require,
            entry.Symlink,
            entry.DigestionSource)).ToImmutableArray();
        return Encoding.UTF8.GetString(FileMapCanonicalWriter.Write(new FileMapManifest(
            policy.Manifest.ResidencePolicy,
            entries,
            policy.ArtifactKinds,
            policy.Manifest.Resources)).AsSpan());
    }

    private static string CurrentManifest(params (string Pattern, string? Plane)[] entries)
    {
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var manifest = new FileMapManifest(policy.Manifest.ResidencePolicy,
            entries.OrderBy(item => item.Pattern, StringComparer.Ordinal).Select(item => new FileMapEntry(
                item.Pattern, FileMapKind.Program,
                item.Plane == "judge" ? FileMapAdmissionPlane.Judge : FileMapAdmissionPlane.Content,
                "none", ["StrataLint"], ["StrataLint"], false, "none", null, "committed-source", null, [], null,
                policy.IsDigestionSource(RepoPath.CreateKnown(item.Pattern)))).ToImmutableArray(),
            policy.ArtifactKinds,
            policy.Manifest.Resources);
        return Encoding.UTF8.GetString(FileMapCanonicalWriter.Write(manifest).AsSpan());
    }

    private static string Manifest(params (string Pattern, string? Plane)[] entries)
    {
        var builder = new StringBuilder(
            "schema_version = 2\n\n"
            + "[residence_policy]\n"
            + "case_id = \"RESIDENCE-EPOCH\"\n"
            + "desired = \"data-must-live-outside-tools\"\n"
            + "known_violation_count = 0\n"
            + "status = \"closed\"\n");
        foreach (var entry in entries.OrderBy(static item => item.Pattern, StringComparer.Ordinal))
        {
            builder.Append($"\n[[files]]\npattern = \"{entry.Pattern}\"\nkind = \"program\"\n");
            if (entry.Plane is not null)
            {
                builder.Append($"admission_plane = \"{entry.Plane}\"\n");
            }

            builder.Append(
                "produced_by = \"none\"\n"
                + "consumed_by = [\"StrataLint\"]\n"
                + "verified_by = [\"StrataLint\"]\n"
                + "artifact_id = \"none\"\n"
                + "runtime_disposition = \"committed-source\"\n");
        }

        return builder.ToString();
    }

    private static RawRepositorySnapshot Snapshot(
        IReadOnlyDictionary<string, string> files,
        bool addDefaultFileMap = true)
    {
        var entries = files.Select(static pair => Entry(pair.Key, pair.Value)).ToList();
        if (addDefaultFileMap && !files.ContainsKey(FileMapPath))
        {
            entries.Add(Entry(FileMapPath, DefaultAdmissionPlaneFileMap));
        }

        return RawRepositorySnapshot.Create(entries);

        static RawRepositoryEntry Entry(string path, string content) => new(
            path,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(content)),
            FrozenLedgerTestData.GitBlobOid(content));
    }
}
