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
        consumed_by = ["AdmissionPlaneDeltaPolicy"]
        verified_by = ["AdmissionPlaneDeltaPolicy"]
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
                    "Meta/FILEMAP.toml",
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

    private static void InstallAdmissionPlaneFileMap(RuleFixture fixture)
    {
        const string manifest = """
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Blueprint/**/*.md"
            kind = "program"
            admission_plane = "content"
            produced_by = "none"
            consumed_by = ["AdmissionPlaneDeltaPolicy"]
            verified_by = ["AdmissionPlaneDeltaPolicy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"

            [[files]]
            pattern = "Meta/FILEMAP.toml"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["AdmissionPlaneDeltaPolicy"]
            verified_by = ["AdmissionPlaneDeltaPolicy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"

            [[files]]
            pattern = "tools/**"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["AdmissionPlaneDeltaPolicy"]
            verified_by = ["AdmissionPlaneDeltaPolicy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n";
        fixture.Files[FileMapPath] = manifest;
        fixture.Baseline[FileMapPath] = manifest;
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
