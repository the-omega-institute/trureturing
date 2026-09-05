using System.Collections.Immutable;
using System.Text.RegularExpressions;
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
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        IReadOnlyCollection<string> protectedBaseControllerInputs,
        IReadOnlyCollection<string> candidateControllerInputs,
        bool full = false)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(protectedBaseControllerInputs);
        ArgumentNullException.ThrowIfNull(candidateControllerInputs);

        var plan = EvaluateOrdinary(
            changedPaths,
            RepositoryRules.ReadSnapshotProjects(protectedBase),
            RepositoryRules.ReadSnapshotProjects(candidate),
            full);
        if (full) return plan;

        var protectedClosure = ScriptTestGateClosurePolicy.Derive(
            protectedBase,
            protectedBaseControllerInputs);
        var candidateClosure = ScriptTestGateClosurePolicy.Derive(
            candidate,
            candidateControllerInputs);
        return ApplyScriptTestGate(
            plan,
            plan.ChangedPaths.Any(path => protectedClosure.Covers(path)
                || candidateClosure.Covers(path)));
    }

    internal static EngineeringTestPlan EvaluateOrdinary(
        IReadOnlyList<string> changedPaths,
        TestProjectTopologySnapshot protectedBase,
        TestProjectTopologySnapshot candidate,
        bool full = false)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);

        var changed = changedPaths
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var baseProjects = protectedBase.Projects
            .Select(ParseProject)
            .OrderBy(static project => project.Path, StringComparer.Ordinal)
            .ToArray();
        var baseTestProjects = baseProjects
            .Where(static project => project.Classification == ProjectClassification.Test)
            .Select(static project => project.Path)
            .ToImmutableArray();
        var baseProjectPaths = baseProjects
            .Select(static project => project.Path)
            .ToHashSet(StringComparer.Ordinal);
        var candidateAddedTestProjects = candidate.Projects
            .Select(ParseProject)
            .Where(project => !baseProjectPaths.Contains(project.Path))
            .Select(project => project.Classification switch
            {
                ProjectClassification.Test => project.Path,
                ProjectClassification.NonTest => null,
                _ => throw new InvalidDataException(
                    $"candidate-added project has no literal IsTestProject classification: {project.Path}"),
            })
            .Where(static path => path is not null)
            .Select(static path => path!)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var allTestProjects = baseTestProjects
            .Concat(candidateAddedTestProjects)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

        if (full)
        {
            return new EngineeringTestPlan(
                EngineeringTestPlanKind.Full,
                changed,
                allTestProjects,
                "FULL=1 selects every protected-base and candidate-added test project");
        }

        var affected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in changed)
        {
            var owner = FindOwner(baseProjects, path);
            if (owner is null)
            {
                return new EngineeringTestPlan(
                    EngineeringTestPlanKind.Full,
                    changed,
                    allTestProjects,
                    $"changed path {path} has no protected-base project owner; "
                    + $"appended {candidateAddedTestProjects.Length} candidate-added test projects");
            }

            affected.Add(owner.Path);
        }

        ExpandReverseClosure(baseProjects, affected);
        var selected = baseTestProjects
            .Where(affected.Contains)
            .Concat(candidateAddedTestProjects)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return selected.Length == 0
            ? new EngineeringTestPlan(
                EngineeringTestPlanKind.None,
                changed,
                [],
                "candidate delta has no affected protected-base or candidate-added test project")
            : new EngineeringTestPlan(
                EngineeringTestPlanKind.Selected,
                changed,
                selected,
                $"selected {selected.Length} protected-base reverse-dependent or candidate-added test projects");
    }

    private static EngineeringTestPlan ApplyScriptTestGate(
        EngineeringTestPlan plan,
        bool include)
    {
        var projects = plan.Projects.ToHashSet(StringComparer.Ordinal);
        if (include)
        {
            projects.Add(ScriptTestGateClosurePolicy.ProjectPath);
            var includedProjects = projects.Order(StringComparer.Ordinal).ToImmutableArray();
            return plan with
            {
                Kind = plan.Kind == EngineeringTestPlanKind.Full
                    ? EngineeringTestPlanKind.Full
                    : EngineeringTestPlanKind.Selected,
                Projects = includedProjects,
                Reason = plan.Reason + "; ScriptTests gate included by derived closure intersection",
            };
        }

        projects.Remove(ScriptTestGateClosurePolicy.ProjectPath);
        var selected = projects.Order(StringComparer.Ordinal).ToImmutableArray();
        return plan with
        {
            Kind = selected.Length == 0
                ? EngineeringTestPlanKind.None
                : EngineeringTestPlanKind.Selected,
            Projects = selected,
            Reason = plan.Reason + "; ScriptTests gate excluded because the candidate delta misses the derived closure",
        };
    }

    private static ProjectNode? FindOwner(IEnumerable<ProjectNode> projects, string changedPath) =>
        projects
            .Where(project => changedPath == project.Path
                || changedPath.StartsWith(project.Directory + "/", StringComparison.Ordinal)
                || project.CompileIncludes.Any(pattern => GlobCovers(pattern, changedPath)))
            .OrderByDescending(project =>
                changedPath.StartsWith(project.Directory + "/", StringComparison.Ordinal)
                    ? project.Directory.Length
                    : 0)
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
        var classifications = document.Descendants()
            .Where(static element => element.Name.LocalName == "IsTestProject")
            .Select(static element => element.Value.Trim())
            .Distinct(StringComparer.OrdinalIgnoreCase)
            .ToArray();
        // 显式 `IsTestProject` 声明优先于 xunit 启发式。倒过来会把「引用 xunit 但明确
        // 声明自己不是测试项目」的支持库判成测试项目,于是 `dotnet test` 对它不产 TRX,
        // 门以 ENGINEERING_TEST_EVIDENCE_FAILED 判红 —— 见 issue #5516,判例是
        // StrataLint.TestSupport(它为 TestScratchFramework 派生 XunitTestFramework 而必须
        // 引用 xunit,同时明写 IsTestProject=false)。启发式只在【无】显式声明时回落使用。
        var classification = classifications switch
            {
                [] => ScribeProjectCompilationContext.IsXunitProject(project.Content)
                    ? ProjectClassification.Test
                    : ProjectClassification.NonTest,
                [var value] when string.Equals(value, "true", StringComparison.OrdinalIgnoreCase) =>
                    ProjectClassification.Test,
                [var value] when string.Equals(value, "false", StringComparison.OrdinalIgnoreCase) =>
                    ProjectClassification.NonTest,
                _ => ProjectClassification.Ambiguous,
            };
        var references = document.Descendants()
            .Where(static element => element.Name.LocalName == "ProjectReference")
            .Select(static element => (string?)element.Attribute("Include"))
            .Where(static include => !string.IsNullOrWhiteSpace(include))
            .Select(include => ResolveProjectReference(path, include!))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var compileIncludes = document.Descendants()
            .Where(static element => element.Name.LocalName == "Compile")
            .Select(static element => (string?)element.Attribute("Include"))
            .Where(static include => !string.IsNullOrWhiteSpace(include))
            .SelectMany(static include => include!.Split(
                ';',
                StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            .Where(static include => !include.Contains("$(", StringComparison.Ordinal))
            .Select(include => ResolveProjectItem(path, include))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return new ProjectNode(path, directory, classification, references, compileIncludes);
    }

    private static string ResolveProjectReference(string projectPath, string include)
    {
        var directory = projectPath[..(projectPath.LastIndexOf('/') + 1)];
        var referenceUri = new Uri(new Uri(RepositoryUri, directory), include.Replace('\\', '/'));
        return Uri.UnescapeDataString(referenceUri.AbsolutePath.TrimStart('/'));
    }

    private static string ResolveProjectItem(string projectPath, string include) =>
        ResolveProjectReference(projectPath, include);

    private static bool GlobCovers(string pattern, string path)
    {
        var expression = "^" + Regex.Escape(pattern)
            .Replace(@"\*\*/", "(?:.*/)?", StringComparison.Ordinal)
            .Replace(@"\*", "[^/]*", StringComparison.Ordinal)
            .Replace(@"\?", "[^/]", StringComparison.Ordinal) + "$";
        return Regex.IsMatch(
            path,
            expression,
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    }

    private static string NormalizePath(string path) => path.Replace('\\', '/');

    private sealed record ProjectNode(
        string Path,
        string Directory,
        ProjectClassification Classification,
        ImmutableArray<string> References,
        ImmutableArray<string> CompileIncludes);

    private enum ProjectClassification { NonTest, Test, Ambiguous }
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
