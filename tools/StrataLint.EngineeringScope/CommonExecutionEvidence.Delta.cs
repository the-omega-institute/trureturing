using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    internal static (CommonStageRecord Current, TestProjectExecution[] Tests) ValidateDeltaCommon(
        string root, ValidationScope validation, IEnumerable<string> baseProjects,
        ResourceExecutionPlan? plan, string? round)
    {
        if (plan is null)
        {
            var common = ValidateCommon(root, validation, baseProjects);
            return (common.Current, common.Tests.Projects);
        }
        var candidate = Candidate(root, validation.Snapshot);
        var build = ValidateBuild(root, candidate, round, validation);
        RequireSelection(build);
        RequireSelection(Read<CommonStageRecord>(root, CurrentPath));
        TestProjectExecution[] accepted = [];
        if (plan.StageRequired("engineering"))
        {
            _ = ValidateEngineering(root, build, validation, out var tests, out _,
                plan.ResourceRequired("engineering") ? baseProjects : null);
            accepted = tests.Projects;
        }
        return (ValidateCurrent(root, build, validation, out _), accepted);

        void RequireSelection(CommonStageRecord record)
        {
            if (record.Selection is null)
                throw new InvalidDataException("scoped delta requires bound build and current resource selection");
            using var retained = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, record.Selection.Plan)));
            if (!JsonElement.DeepEquals(retained.RootElement, plan.Document))
                throw new InvalidDataException("delta resource selection differs from common evidence");
        }
    }
}
