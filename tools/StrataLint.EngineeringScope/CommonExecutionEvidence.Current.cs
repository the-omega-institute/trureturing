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

    internal static StageStep[] CompleteCurrent(string root, CommonStageRecord build, StageStep[] producerSteps,
        ResourceExecutionPlan? plan = null) => SealCurrent(root, build, producerSteps, plan, completeCheckSteps: true);

    internal static void SealCurrent(string root, CommonStageRecord build, StageStep[] steps, ResourceExecutionPlan? plan = null) =>
        _ = SealCurrent(root, build, steps, plan, completeCheckSteps: false);

    private static StageStep[] SealCurrent(string root, CommonStageRecord build, StageStep[] steps,
        ResourceExecutionPlan? plan, bool completeCheckSteps)
    {
        var candidate = Candidate(root, out var snapshot);
        var validation = new ValidationScope(snapshot);
        ValidateStartedBuild(root, build, candidate, validation);
        var expected = plan?.CurrentSteps ?? CurrentSteps;
        if (!completeCheckSteps) RequirePassed(steps, expected);
        var ids = plan?.CheckUnits.Except(EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray()
            ?? CheckIds("current", ReadCheckManifest(snapshot));
        var reportRequired = expected.Contains("lean-report", StringComparer.Ordinal);
        if (reportRequired)
            validation.Report(Path.Combine(root, ReportPath));
        var checks = ids.Length == 0 ? null : ValidateChecks(root, "current", build, ids, validation);
        // Derive the stage obligations from the checks already validated here.
        // Keep this read-only phase inside one call, without output callbacks.
        if (completeCheckSteps)
        {
            var completed = steps.ToList();
            foreach (var name in expected.Where(name => name is "scribe" or "filemap" or "check-current"))
            {
                var units = checks?.Units.Where(unit => name == "scribe" ? unit.Id.StartsWith("scribe-", StringComparison.Ordinal)
                    : name == "filemap" ? unit.Id == "filemap" : unit.Id.StartsWith("SL-", StringComparison.Ordinal)).ToArray() ?? [];
                if (units.Length == 0) throw new InvalidDataException("missing registered units for required step: " + name);
                completed.Add(new(name, 0, 0, units.All(unit => unit.Status == "reused") ? "reused" : "executed", units[0].Operations[0].Log));
            }
            steps = completed.ToArray();
            RequirePassed(steps, expected);
        }
        // Retain can replace selection files; sealing must read fresh bytes after it.
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
        return steps;
    }

    internal static CommonStageRecord ValidateCurrent(string root) => ValidateCurrent(root, out _);

    private static CommonStageRecord ValidateCurrent(string root, out CommonCheckRecord? checks)
        => ValidateCurrent(root, out checks, out _, out _);

    internal static (CommonStageRecord Current, CommonStageRecord Build, ValidationScope Validation) ValidateCurrentForTransport(string root)
    {
        var current = ValidateCurrent(root, out _, out var build, out var validation);
        return (current, build, validation);
    }

    private static CommonStageRecord ValidateCurrent(string root, out CommonCheckRecord? checks,
        out CommonStageRecord build, out ValidationScope validation)
    {
        var candidate = Candidate(root, out var snapshot);
        validation = new ValidationScope(snapshot);
        build = ValidateBuild(root, candidate, null, validation);
        return ValidateCurrent(root, build, validation, out checks);
    }

    private static CommonStageRecord ValidateCurrent(string root, CommonStageRecord build, RepositorySnapshot snapshot) =>
        ValidateCurrent(root, build, new ValidationScope(snapshot), out _);

    private static CommonStageRecord ValidateCurrent(string root, CommonStageRecord build, ValidationScope validation,
        out CommonCheckRecord? checks)
    {
        var snapshot = validation.Snapshot;
        var record = Read<CommonStageRecord>(root, CurrentPath);
        ValidateRecord(root, record, build.Candidate, build.Round, validation);
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
        checks = ids.Length == 0 ? null : ValidateChecks(root, "current", build, ids, validation);
        if (expected.Contains("lean-report"))
            validation.Report(Path.Combine(root, ReportPath));
        return record;
    }
}
