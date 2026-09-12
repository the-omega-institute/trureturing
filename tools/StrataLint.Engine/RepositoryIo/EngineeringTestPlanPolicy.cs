using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }
internal sealed record EngineeringTestPlan(
    EngineeringTestPlanKind Kind, ImmutableArray<string> ChangedPaths,
    ImmutableArray<string> Projects, string Reason);
internal sealed record EngineeringTestInvocation(string ProjectPath);

internal static class EngineeringTestPlanPolicy
{
    // CI exclusion only. The canonical local solution test still runs this project.
    private const string ContinuousIntegrationExclusion =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";

    internal static EngineeringTestPlan EvaluateOrdinary(
        IReadOnlyList<string> changedPaths, EngineeringInputManifest manifest, bool full = false)
    {
        var changed = changedPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
        var affected = new HashSet<string>(StringComparer.Ordinal);
        // Full execution does not excuse incomplete registration.
        foreach (var path in changed) affected.UnionWith(manifest.Owners(path));
        ExpandReverseClosure(manifest.Projects, affected);
        var selected = manifest.Projects
            .Where(project => EngineeringInputManifest.IsTest(project)
                && project.Path != ContinuousIntegrationExclusion
                && (full || affected.Contains(project.Path)))
            .Select(project => project.Path).Order(StringComparer.Ordinal).ToImmutableArray();
        return new(selected.IsEmpty ? EngineeringTestPlanKind.None : full ? EngineeringTestPlanKind.Full : EngineeringTestPlanKind.Selected,
            changed, selected, selected.IsEmpty
                ? "not-required: complete registered inputs select no CI test resources"
                : "explicit registered input and impact declarations");
    }

    private static void ExpandReverseClosure(IEnumerable<EngineeringProject> projects, ISet<string> affected)
    {
        bool added;
        do
        {
            added = false;
            foreach (var project in projects)
                if (project.References.Any(affected.Contains) && affected.Add(project.Path)) added = true;
        } while (added);
    }
}

internal static class EngineeringTestExecutor
{
    internal static int Execute(
        EngineeringTestPlan plan,
        Func<EngineeringTestInvocation, int> run)
    {
        if (plan.Projects.Length == 0) return 0;

        var exitCodes = new int[plan.Projects.Length];
        var options = new ParallelOptions
        {
            MaxDegreeOfParallelism = Math.Min(
                Environment.ProcessorCount,
                plan.Projects.Length),
        };
        Parallel.For(0, plan.Projects.Length, options, projectIndex =>
            exitCodes[projectIndex] = run(
                new EngineeringTestInvocation(plan.Projects[projectIndex])));

        return exitCodes.FirstOrDefault(static exitCode => exitCode != 0);
    }
}
