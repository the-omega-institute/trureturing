using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    private static IEnumerable<string> SelectionPaths(ResourcePlanBinding? selection) =>
        selection is null ? [] : new[] { selection.Plan, selection.Changes };

    private static ResourceExecutionPlan? CurrentPlan(string root, CommonStageRecord record) =>
        record.Selection is null ? null : ResourceExecutionPlan.Load(root,
            Path.Combine(root, record.Selection.Plan), Path.Combine(root, record.Selection.Changes));

    internal static string[] CurrentCheckIds(string root) =>
        CurrentPlan(root, Read<CommonStageRecord>(root, CurrentPath))?.CheckUnits
            .Except(EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray()
        ?? CheckIds("current", ReadCheckManifest(Snapshot(root)));

    internal static void SealCurrent(string root, CommonStageRecord build, StageStep[] steps, ResourceExecutionPlan? plan = null)
    {
        var candidate = Candidate(root, out var snapshot);
        ValidateStartedBuild(root, build, candidate);
        var expected = plan?.CurrentSteps ?? CurrentSteps;
        RequirePassed(steps, expected);
        var ids = plan?.CheckUnits.Except(EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray()
            ?? CheckIds("current", ReadCheckManifest(snapshot));
        var reportRequired = expected.Contains("lean-report", StringComparer.Ordinal);
        if (reportRequired)
            _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
        var checks = ids.Length == 0 ? null : ValidateChecks(root, "current", build, ids);
        var selection = plan?.Retain(root);
        var materials = (reportRequired ? ReportPaths : []).Append(BuildPath)
            .Concat(SelectionPaths(selection))
            .Concat(checks is null ? [] : new[] { ChecksPath("current"), CheckManifestPath })
            .Concat(checks?.Units.SelectMany(unit => unit.Materials).Select(material => material.Path) ?? [])
            .Concat(ids.Contains("scribe-markdown") ? new[] { ScribeMarkdownPaths }.Where(path => File.Exists(Path.Combine(root, path))) : [])
            .Concat(steps.Select(step => step.Log));
        var record = new CommonStageRecord(2, candidate, build.Round, steps, Materials(root, materials), selection);
        Write(root, CurrentPath, record);
        WriteBundleList(root, "current", build.Materials.Concat(record.Materials).Select(material => material.Path).Append(CurrentPath));
    }

    internal static CommonStageRecord ValidateCurrent(string root) => ValidateCurrent(root, out _);

    private static CommonStageRecord ValidateCurrent(string root, out CommonCheckRecord? checks)
    {
        var candidate = Candidate(root, out var snapshot);
        return ValidateCurrent(root, ValidateBuild(root, candidate, null), snapshot, out checks);
    }

    private static CommonStageRecord ValidateCurrent(string root, CommonStageRecord build, RepositorySnapshot snapshot) =>
        ValidateCurrent(root, build, snapshot, out _);

    private static CommonStageRecord ValidateCurrent(string root, CommonStageRecord build, RepositorySnapshot snapshot,
        out CommonCheckRecord? checks)
    {
        var record = Read<CommonStageRecord>(root, CurrentPath);
        ValidateRecord(root, record, build.Candidate, build.Round);
        var plan = CurrentPlan(root, record);
        var expected = plan?.CurrentSteps ?? CurrentSteps;
        RequirePassed(record.Steps, expected);
        var ids = plan?.CheckUnits.Except(EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray()
            ?? CheckIds("current", ReadCheckManifest(snapshot));
        var required = new[] { BuildPath }.Concat(SelectionPaths(record.Selection))
            .Concat(ids.Length == 0 ? [] : new[] { ChecksPath("current"), CheckManifestPath })
            .Concat(expected.Contains("lean-report") ? ReportPaths : []);
        if (required.Any(path => !record.Materials.Any(material => material.Path == path)))
            throw new InvalidDataException("current has missing required materials");
        if (!expected.Contains("lean-report") && record.Materials.Any(material => ReportPaths.Contains(material.Path)))
            throw new InvalidDataException("unrequested report cannot be current evidence");
        checks = ids.Length == 0 ? null : ValidateChecks(root, "current", build, ids);
        if (expected.Contains("lean-report"))
            _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
        return record;
    }
}
