using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string FileMapPath = "Meta/FILEMAP.toml";
    private const string DefaultAdmissionPlaneFileMap = """
        schema_version = 2

        [residence_policy]
        case_id = "RESIDENCE-EPOCH"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"

        [[files]]
        pattern = "**"
        kind = "program"
        admission_plane = "content"
        produced_by = "none"
        consumed_by = ["StrataLint"]
        verified_by = ["StrataLint"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """ + "\n";

    [Fact]
    public void MixedJudgeAndContentDeltaIsRejectedByCandidateCheck()
    {
        var fixture = TrustedFrozenFixture();
        InstallAdmissionPlaneFileMap(fixture);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(
                [
                    RuleFixture.SyntheticProtectedPath,
                    RuleFixture.BlueprintPath,
                ]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics,
            static item => item.Message.Contains(
                "ADMISSION-PLANE-MIXED",
                StringComparison.Ordinal));
        Assert.Equal(RuleId.CreateKnown(29), diagnostic.RuleId);
        Assert.Equal("Admission plane partition", diagnostic.Title);
        Assert.Equal(DisplaySeverity.Error, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void CandidateFileMapEntryAndNewJudgeFileInSameDeltaAreAdmissibleAndJudgeOnly()
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
            [FileMapPath, newPath]);
        var outcome = CheckWithReports(environment, fixture);

        Assert.True(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.JudgeOnly, decision.Classification);
        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void CandidateFileMapWithoutNewJudgeEntryFailsClosedForSameDelta()
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
            [FileMapPath, newPath]);
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

    [Fact]
    public void JudgeOnlyDeltaRemainsAdmissible()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            out var usedBootstrap,
            "tools/change.cs");

        Assert.Null(outcome);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void ContentOnlyDeltaRemainsAdmissible()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            out var usedBootstrap,
            "docs/change.md");

        Assert.Null(outcome);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void RealGitCopyClassifiesOnlyAddedDestination()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(
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
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = ReviewRegressionTests.RunGit(
            repository.Path,
            "rev-parse",
            "HEAD").Trim();
        File.Copy(sourcePath, destinationPath);
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "candidate");
        var gateway = new GitRepositoryGateway(repository.Path);

        var prepared = gateway.Prepare(baseline);
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            gateway.ReadRevision(baseline),
            prepared.Changes,
            out var usedBootstrap);

        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "judge/source.txt" && change.Kind == RawChangeKind.Copied);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "content/copy.txt" && change.Kind == RawChangeKind.Added);
        Assert.Null(outcome);
        Assert.False(usedBootstrap);
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
            changes,
            out var usedBootstrap);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, static item =>
            item.Message.Contains("ADMISSION-PLANE-MIXED", StringComparison.Ordinal));
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void EmptyDeltaRemainsAdmissible()
    {
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot([0xff]),
            RawChangeSet.Create([]),
            out var usedBootstrap);

        Assert.Null(outcome);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void UnmatchedPathFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "content")),
            out _,
            "tools/change.cs");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("path=tools/change.cs matches=0", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MultiplyMatchedPathFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "content"), ("docs/*.md", "content")),
            out _,
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("path=docs/change.md matches=2", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAdmissionPlaneFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", null)),
            out _,
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-ADMISSION-PLANE-MISSING", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void InvalidAdmissionPlaneFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/**", "observer")),
            out _,
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-ADMISSION-PLANE-INVALID", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void QuestionMarkPatternFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest(("docs/?.md", "content")),
            out _,
            "docs/a.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP-PATTERN-UNSAFE", failure.Message, StringComparison.Ordinal);
        Assert.Contains("docs/?.md", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateFileMapUnavailableFailsClosed()
    {
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot(null),
            RawChangeSet.Create(["docs/change.md"]),
            out var usedBootstrap);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP is unavailable", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("protected-base", failure.Message, StringComparison.Ordinal);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void CandidateFileMapUnparseableFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            "files = [\n",
            out var usedBootstrap,
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP cannot be parsed", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("protected-base", failure.Message, StringComparison.Ordinal);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void ClassifiableLegacyFileMapIgnoresNonCoreFormattingAndFields()
    {
        var legacy = "schema_version = 1\r\n"
            + "legacy_metadata = true\r\n"
            + "[[files]]\r\n"
            + "pattern = \"docs/**\"\r\n"
            + "admission_plane = \"content\"";

        var outcome = EvaluateAdmissionPlane(legacy, out var usedBootstrap, "docs/change.md");

        Assert.Null(outcome);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void InlineTableFileArrayIsClassified()
    {
        var outcome = EvaluateAdmissionPlane(
            "files = [{ pattern = \"docs/**\", admission_plane = \"content\" }]\n",
            out var usedBootstrap,
            "docs/change.md");

        Assert.Null(outcome);
        Assert.False(usedBootstrap);
    }


    private static AdmissionOutcome? EvaluateAdmissionPlane(
        string manifest,
        out bool usedBootstrap,
        params string[] changedPaths) =>
        ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot(Encoding.UTF8.GetBytes(manifest)),
            RawChangeSet.Create(changedPaths),
            out usedBootstrap);

    private static RawRepositorySnapshot AdmissionPlaneSnapshot(byte[]? fileMapBytes) =>
        RawRepositorySnapshot.Create(fileMapBytes is null
            ? []
            : [new RawRepositoryEntry(FileMapPath, ImmutableArray.CreateRange(fileMapBytes))]);

    private static void InstallAdmissionPlaneFileMap(RuleFixture fixture)
    {
        var manifest = Manifest(
            ("Blueprint/**/*.md", "content"),
            (FileMapPath, "judge"),
            ("tools/**", "judge"));
        fixture.Files[FileMapPath] = manifest;
        fixture.Baseline[FileMapPath] = manifest;
    }

    private static void InstallCandidateFileMapDelta(
        RuleFixture fixture,
        string newPath,
        bool includeNewPath)
    {
        var baselinePaths = fixture.Baseline.Keys
            .Append(FileMapPath)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        fixture.Baseline[FileMapPath] = Manifest(baselinePaths
            .Select(static path => (
                path,
                Plane: (string?)(path == FileMapPath ? "judge" : "content")))
            .ToArray());
        fixture.Files[newPath] = "internal sealed class Program { }\n";
        fixture.Files[FileMapPath] = Manifest(baselinePaths
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

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files)
    {
        var entries = files.Select(static pair => Entry(pair.Key, pair.Value)).ToList();
        if (!files.ContainsKey(FileMapPath))
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
