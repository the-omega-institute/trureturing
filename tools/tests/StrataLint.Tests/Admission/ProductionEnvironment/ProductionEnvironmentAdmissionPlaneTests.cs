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

    private static string CiPath => ".github/" + "work" + "flows/ci.yml";

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
        Assert.Contains(
            rejected.Diagnostics,
            static diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Message.Contains(
                    "ADMISSION-PLANE-MIXED",
                    StringComparison.Ordinal));
    }

    [Fact]
    public void CandidateRelabelOfBaseContentPatternDoesNotChangeClassification()
    {
        var fixture = TrustedFrozenFixture();
        InstallAdmissionPlaneFileMap(fixture);
        fixture.Files[FileMapPath] = fixture.Files[FileMapPath].Replace(
            "pattern = \"Blueprint/**/*.md\"\nkind = \"program\"\nadmission_plane = \"content\"",
            "pattern = \"Blueprint/**/*.md\"\nkind = \"program\"\nadmission_plane = \"judge\"",
            StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(
                [
                    FileMapPath,
                    RuleFixture.BlueprintPath,
                ]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            static diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Message.Contains(
                    "ADMISSION-PLANE-MIXED",
                    StringComparison.Ordinal));
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
    public void FileMapRepairBootstrapRemainsNarrow()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest((CiPath, "judge"), (FileMapPath, "judge")),
            out var usedBootstrap,
            CiPath,
            FileMapPath);

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
    public void BaseFileMapUnavailableFailsClosedOutsideRepair()
    {
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot(null),
            RawChangeSet.Create(["docs/change.md"]),
            out var usedBootstrap);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("protected-base FILEMAP is unavailable", failure.Message, StringComparison.Ordinal);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void BaseFileMapUnparseableFailsClosedOutsideRepair()
    {
        var outcome = EvaluateAdmissionPlane(
            "files = [\n",
            out var usedBootstrap,
            "docs/change.md");

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("protected-base FILEMAP cannot be parsed", failure.Message, StringComparison.Ordinal);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void InvalidFileMapSchemaDuringRepairFailsClosed()
    {
        var invalid = Manifest((CiPath, "judge"), (FileMapPath, "judge")).Replace(
            "schema_version = 2",
            "schema_version = 1",
            StringComparison.Ordinal);

        var outcome = EvaluateAdmissionPlane(invalid, out var usedBootstrap, FileMapPath);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("schema_version must be 2", failure.Message, StringComparison.Ordinal);
        Assert.False(usedBootstrap);
    }

    [Fact]
    public void ReservedRepairPathNotOnJudgePlaneFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest((CiPath, "judge"), (FileMapPath, "content")),
            out _,
            FileMapPath);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(
            $"reserved repair path must resolve once to judge: {FileMapPath}",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingReservedRepairPathFailsClosed()
    {
        var outcome = EvaluateAdmissionPlane(
            Manifest((FileMapPath, "judge")),
            out _,
            FileMapPath);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(
            $"reserved repair path must resolve once to judge: {CiPath}",
            failure.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RepairWithUnavailableBaseFileMapUsesBootstrap()
    {
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            AdmissionPlaneSnapshot(null),
            RawChangeSet.Create([FileMapPath]),
            out var usedBootstrap);

        Assert.Null(outcome);
        Assert.True(usedBootstrap);
    }

    [Fact]
    public void RepairWithMalformedBaseFileMapUsesBootstrap()
    {
        var outcome = EvaluateAdmissionPlane(
            "files = [\n",
            out var usedBootstrap,
            FileMapPath);

        Assert.Null(outcome);
        Assert.True(usedBootstrap);
    }

    [Fact]
    public void RepairWithInvalidUtf8BaseFileMapCompletesCandidateCheck()
    {
        var fixture = TrustedFrozenFixture();
        InstallRepairAdmissionPlaneFileMap(fixture);
        var baseline = ReplaceFileMapBytes(Snapshot(fixture.Baseline), [0xff, (byte)'\n']);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([FileMapPath]),
                Snapshot(fixture.Files),
                baseline),
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
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

    private static RawRepositorySnapshot ReplaceFileMapBytes(
        RawRepositorySnapshot snapshot,
        byte[] bytes) =>
        RawRepositorySnapshot.Create(
            snapshot.Entries
                .Where(static entry => entry.Path != FileMapPath)
                .Append(new RawRepositoryEntry(FileMapPath, ImmutableArray.CreateRange(bytes))));

    private static void InstallAdmissionPlaneFileMap(RuleFixture fixture)
    {
        var manifest = Manifest(
            ("Blueprint/**/*.md", "content"),
            (FileMapPath, "judge"),
            ("tools/**", "judge"));
        fixture.Files[FileMapPath] = manifest;
        fixture.Baseline[FileMapPath] = manifest;
    }

    private static void InstallRepairAdmissionPlaneFileMap(RuleFixture fixture)
    {
        var manifest = Manifest((CiPath, "judge"), (FileMapPath, "judge"));
        fixture.Files[FileMapPath] = manifest;
        fixture.Baseline[FileMapPath] = manifest;
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
