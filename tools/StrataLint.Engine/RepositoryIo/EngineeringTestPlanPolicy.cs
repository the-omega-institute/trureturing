using System.Collections.Immutable;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }

internal sealed record EngineeringTestPlan(
    EngineeringTestPlanKind Kind,
    ImmutableArray<string> ChangedPaths,
    ImmutableArray<string> Projects,
    ImmutableArray<string> RemovedBaseTestProjects,
    string Reason);

internal sealed record EngineeringTestInvocation(string ProjectPath);

internal static class EngineeringTestPlanPolicy
{
    private static readonly Uri RepositoryUri = new("https://repository.invalid/");

    // CI 的测试执行计划永不选中的项目(owner 2026-09-07)。
    //
    // `StrataLint.ScriptTests` 的被测对象是仓库 shell 脚本与 make target:它能证合成夹具里
    // 打印了什么,不能证真实管线会不会正确执行 —— 器律⑦′ 对 workflow 的同一判断,此处施于
    // 脚本。而它的代价是实测的:2026-09-07 一天内这族测试三次阻塞无关 PR(#4873、#5249、
    // #5060 与 #5672),此前决定「何时跑它」的那台派生闭包机器自身也打过两个解全仓阻塞的
    // hotfix(13b3f08eb5、b9770f831b)。
    //
    // 测试**保留在树上**:`make -C tools test` 跑整个解决方案,本地照跑;移出的只是 CI 的
    // 判据面。判据由「碰了派生闭包才跑」变成常量「从不」,故那台派生机器随本次改动退役。
    private static readonly ImmutableArray<string> ContinuousIntegrationExclusions =
    [
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj",
    ];

    private static bool IsExcludedFromContinuousIntegration(string projectPath) =>
        ContinuousIntegrationExclusions.Contains(projectPath, StringComparer.Ordinal);

    internal static EngineeringTestPlan EvaluateOrdinary(
        IReadOnlyList<string> changedPaths,
        TestProjectTopologySnapshot protectedBase,
        TestProjectTopologySnapshot candidate,
        bool full = false,
        AdmissionPlaneDecision? admissionPlane = null)
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
            .Where(static path => !IsExcludedFromContinuousIntegration(path))
            .ToImmutableArray();
        var baseProjectPaths = baseProjects
            .Select(static project => project.Path)
            .ToHashSet(StringComparer.Ordinal);
        var candidateProjects = candidate.Projects
            .Select(ParseProject)
            .OrderBy(static project => project.Path, StringComparer.Ordinal)
            .ToArray();
        var candidateProjectPaths = candidateProjects
            .Select(static project => project.Path)
            .ToHashSet(StringComparer.Ordinal);
        var removedBaseTestProjects = baseTestProjects
            .Where(project => !candidateProjectPaths.Contains(project))
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var candidatePresentBaseTestProjects = baseTestProjects
            .Where(candidateProjectPaths.Contains)
            .ToImmutableArray();
        var candidateAddedTestProjects = candidateProjects
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
            .Where(static path => !IsExcludedFromContinuousIntegration(path))
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var allTestProjects = candidatePresentBaseTestProjects
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
                removedBaseTestProjects,
                "FULL=1 selects every candidate-present protected-base and candidate-added test project");
        }

        var unownedDigestionData = admissionPlane is
            { IsAdmissible: true, Classification: AdmissionPlaneClassification.ContentOnly }
            && changed.Length > 0
            && changed.All(static path => BackfillInventoryLoader.IsCanonicalPath(path)
                || DigestionCasStore.IsCanonicalPath(path));
        var affected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in changed)
        {
            var owner = FindOwner(baseProjects, path);
            if (owner is null)
            {
                if (unownedDigestionData) continue;

                return new EngineeringTestPlan(
                    EngineeringTestPlanKind.Full,
                    changed,
                    allTestProjects,
                    removedBaseTestProjects,
                    $"changed path {path} has no protected-base project owner; "
                    + $"appended {candidateAddedTestProjects.Length} candidate-added test projects");
            }

            affected.Add(owner.Path);
        }

        ExpandReverseClosure(baseProjects, affected);
        var selected = candidatePresentBaseTestProjects
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
                removedBaseTestProjects,
                "candidate delta has no affected protected-base or candidate-added test project")
            : new EngineeringTestPlan(
                EngineeringTestPlanKind.Selected,
                changed,
                selected,
                removedBaseTestProjects,
                $"selected {selected.Length} candidate-present protected-base reverse-dependent or candidate-added test projects");
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
