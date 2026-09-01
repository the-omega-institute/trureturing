using System.Collections.Immutable;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }

internal sealed record EngineeringTestPlan(
    EngineeringTestPlanKind Kind,
    ImmutableArray<string> ChangedPaths,
    ImmutableArray<string> Projects,
    string Reason);

internal sealed record EngineeringTestInvocation(string ProjectPath);

internal static class EngineeringTestPlanPolicy
{
    private static readonly Uri RepositoryUri = new("https://repository.invalid/");

    internal static EngineeringTestPlan Evaluate(
        IReadOnlyList<string> changedPaths,
        TestProjectTopologySnapshot protectedBase,
        bool full = false)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        ArgumentNullException.ThrowIfNull(protectedBase);

        var changed = changedPaths
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var projects = protectedBase.Projects
            .Select(ParseProject)
            .OrderBy(static project => project.Path, StringComparer.Ordinal)
            .ToArray();
        var testProjects = projects
            .Where(static project => project.IsTest)
            .Select(static project => project.Path)
            .ToImmutableArray();

        if (full)
        {
            return new EngineeringTestPlan(
                EngineeringTestPlanKind.Full,
                changed,
                testProjects,
                "FULL=1 selects every protected-base test project");
        }

        var affected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in changed)
        {
            var owner = FindOwner(projects, path);
            if (owner is null)
            {
                return new EngineeringTestPlan(
                    EngineeringTestPlanKind.Full,
                    changed,
                    testProjects,
                    $"changed path {path} has no protected-base project owner");
            }

            affected.Add(owner.Path);
        }

        ExpandReverseClosure(projects, affected);
        var selected = testProjects.Where(affected.Contains).ToImmutableArray();
        return selected.Length == 0
            ? new EngineeringTestPlan(
                EngineeringTestPlanKind.None,
                changed,
                [],
                "candidate delta has no affected protected-base test project")
            : new EngineeringTestPlan(
                EngineeringTestPlanKind.Selected,
                changed,
                selected,
                $"selected {selected.Length} protected-base reverse-dependent test projects");
    }

    private static ProjectNode? FindOwner(IEnumerable<ProjectNode> projects, string changedPath) =>
        projects
            .Where(project => changedPath == project.Path
                || changedPath.StartsWith(project.Directory + "/", StringComparison.Ordinal))
            .OrderByDescending(static project => project.Directory.Length)
            .ThenBy(static project => project.Path, StringComparer.Ordinal)
            .FirstOrDefault();

    private static void ExpandReverseClosure(
        IReadOnlyList<ProjectNode> projects,
        ISet<string> affected)
    {
        var added = true;
        while (added)
        {
            added = false;
            foreach (var project in projects)
            {
                if (!affected.Contains(project.Path)
                    && project.References.Any(affected.Contains)
                    && affected.Add(project.Path))
                {
                    added = true;
                }
            }
        }
    }

    private static ProjectNode ParseProject(TestProjectTopologyProject project)
    {
        var path = NormalizePath(project.Path);
        var directory = path[..path.LastIndexOf('/')];
        var document = XDocument.Parse(project.Content, LoadOptions.None);
        var isTest = document.Descendants().Any(static element =>
            element.Name.LocalName == "IsTestProject"
            && string.Equals(element.Value.Trim(), "true", StringComparison.OrdinalIgnoreCase));
        var references = document.Descendants()
            .Where(static element => element.Name.LocalName == "ProjectReference")
            .Select(static element => (string?)element.Attribute("Include"))
            .Where(static include => !string.IsNullOrWhiteSpace(include))
            .Select(include => ResolveProjectReference(path, include!))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return new ProjectNode(path, directory, isTest, references);
    }

    private static string ResolveProjectReference(string projectPath, string include)
    {
        var directory = projectPath[..(projectPath.LastIndexOf('/') + 1)];
        var referenceUri = new Uri(new Uri(RepositoryUri, directory), include.Replace('\\', '/'));
        return Uri.UnescapeDataString(referenceUri.AbsolutePath.TrimStart('/'));
    }

    private static string NormalizePath(string path) => path.Replace('\\', '/');

    private sealed record ProjectNode(
        string Path,
        string Directory,
        bool IsTest,
        ImmutableArray<string> References);
}

internal static class EngineeringTestExecutor
{
    internal static int Execute(
        EngineeringTestPlan plan,
        Func<EngineeringTestInvocation, int> run)
    {
        foreach (var project in plan.Projects)
        {
            var exitCode = run(new EngineeringTestInvocation(project));
            if (exitCode != 0) return exitCode;
        }

        return 0;
    }
}
