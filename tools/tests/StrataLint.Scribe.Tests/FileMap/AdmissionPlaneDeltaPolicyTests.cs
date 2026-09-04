using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class AdmissionPlaneDeltaPolicyTests
{
    private static string CiPath => ".github/" + "work" + "flows/ci.yml";

    [Fact]
    public void JudgeOnlyDeltaRemainsAdmissible()
    {
        var decision = Decide(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "tools/change.cs");

        Assert.True(decision.IsAdmissible, decision.Message);
        Assert.Equal(AdmissionPlaneDeltaClassification.JudgeOnly, decision.Classification);
        Assert.True(decision.RequiresFullEngineering());
    }

    [Fact]
    public void ContentOnlyDeltaRemainsAdmissible()
    {
        var decision = Decide(
            Manifest(("tools/**", "judge"), ("docs/**", "content")),
            "docs/change.md");

        Assert.True(decision.IsAdmissible, decision.Message);
        Assert.Equal(AdmissionPlaneDeltaClassification.ContentOnly, decision.Classification);
        Assert.False(decision.RequiresFullEngineering());
    }

    [Fact]
    public void EmptyDeltaRemainsAdmissible()
    {
        var decision = Decide("not TOML");

        Assert.True(decision.IsAdmissible, decision.Message);
        Assert.Equal(AdmissionPlaneDeltaClassification.Empty, decision.Classification);
        Assert.False(decision.RequiresFullEngineering());
    }

    [Fact]
    public void FileMapRepairBootstrapRemainsNarrow()
    {
        var changes = RawChangeSet.Create([CiPath, FileMapLoader.RelativePath]);
        var available = AdmissionPlaneDeltaPolicy.Evaluate(
            Encoding.UTF8.GetBytes(Manifest(
                ((string)CiPath, "judge"),
                (FileMapLoader.RelativePath, "judge"))),
            changes);
        var unavailable = AdmissionPlaneDeltaPolicy.EvaluateUnavailable(changes);

        Assert.True(available.IsAdmissible, available.Message);
        Assert.Equal(AdmissionPlaneDeltaClassification.JudgeOnly, available.Classification);
        Assert.True(available.RequiresFullEngineering());
        Assert.True(unavailable.IsAdmissible, unavailable.Message);
        Assert.Equal(AdmissionPlaneDeltaClassification.Bootstrap, unavailable.Classification);
        Assert.True(unavailable.RequiresFullEngineering());
    }

    [Fact]
    public void UnmatchedPathFailsClosed()
    {
        var decision = Decide(Manifest(("docs/**", "content")), "tools/change.cs");

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-PATH-MATCH-COUNT", decision.Code);
        Assert.Contains("matches=0", decision.Message, StringComparison.Ordinal);
        Assert.Throws<InvalidOperationException>(() => decision.RequiresFullEngineering());
    }

    [Fact]
    public void MultiplyMatchedPathFailsClosed()
    {
        var decision = Decide(
            Manifest(("docs/**", "content"), ("docs/*.md", "content")),
            "docs/change.md");

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-PATH-MATCH-COUNT", decision.Code);
        Assert.Contains("matches=2", decision.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("")]
    [InlineData("observer")]
    public void MissingOrInvalidAdmissionPlaneFailsClosed(string admissionPlane)
    {
        var source = Manifest(("docs/**", "content"));
        source = admissionPlane.Length == 0
            ? source.Replace("admission_plane = \"content\"\n", "", StringComparison.Ordinal)
            : source.Replace(
                "admission_plane = \"content\"",
                $"admission_plane = \"{admissionPlane}\"",
                StringComparison.Ordinal);

        var decision = Decide(source, "docs/change.md");

        Assert.False(decision.IsAdmissible);
        Assert.Equal(
            admissionPlane.Length == 0
                ? "FILEMAP-ADMISSION-PLANE-MISSING"
                : "FILEMAP-ADMISSION-PLANE-INVALID",
            decision.Code);
    }

    [Fact]
    public void QuestionMarkPatternFailsClosed()
    {
        var decision = Decide(Manifest(("docs/?.md", "content")), "docs/a.md");

        Assert.False(decision.IsAdmissible);
        Assert.Equal(FileMapPatternException.FindingCode, decision.Code);
        Assert.Equal("docs/?.md", decision.Path);
    }

    [Fact]
    public void BaseFileMapUnavailableFailsClosedOutsideRepair()
    {
        var decision = AdmissionPlaneDeltaPolicy.EvaluateUnavailable(
            RawChangeSet.Create(["docs/change.md"]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-BASE-FILEMAP-UNAVAILABLE", decision.Code);
    }

    [Fact]
    public void ReservedRepairPathNotOnJudgePlaneFailsClosed()
    {
        var decision = Decide(
            Manifest(
                ((string)CiPath, "judge"),
                (FileMapLoader.RelativePath, "content")),
            FileMapLoader.RelativePath);

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-REPAIR-PATH-NOT-JUDGE", decision.Code);
        Assert.Equal(FileMapLoader.RelativePath, decision.Path);
    }

    private static AdmissionPlaneDeltaDecision Decide(
        string manifest,
        params string[] changedPaths) =>
        AdmissionPlaneDeltaPolicy.Evaluate(
            Encoding.UTF8.GetBytes(manifest),
            RawChangeSet.Create(changedPaths));

    private static string Manifest(params (string Pattern, string Plane)[] entries)
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
            builder.Append(
                $"\n[[files]]\npattern = \"{entry.Pattern}\"\n"
                + "kind = \"program\"\n"
                + $"admission_plane = \"{entry.Plane}\"\n"
                + "produced_by = \"none\"\n"
                + "consumed_by = [\"AdmissionPlaneDeltaPolicy\"]\n"
                + "verified_by = [\"AdmissionPlaneDeltaPolicy\"]\n"
                + "artifact_id = \"none\"\n"
                + "runtime_disposition = \"committed-source\"\n");
        }

        return builder.ToString();
    }
}
