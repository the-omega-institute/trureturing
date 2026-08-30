using System.Collections.Immutable;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record TestProjectTopologyProject(
    string Path,
    string Content);

internal sealed record TestProjectTopologySnapshot(
    IReadOnlyList<TestProjectTopologyProject> Projects);

internal sealed class TestProjectTopologyDebt : IEquatable<TestProjectTopologyDebt>
{
    internal TestProjectTopologyDebt(string kind, string subject, string related)
    {
        Kind = kind;
        Subject = subject;
        Related = related;
    }

    internal string Kind { get; }

    internal string Subject { get; }

    internal string Related { get; }

    public bool Equals(TestProjectTopologyDebt? other) =>
        other is not null
        && string.Equals(Kind, other.Kind, StringComparison.Ordinal)
        && string.Equals(Subject, other.Subject, StringComparison.OrdinalIgnoreCase)
        && string.Equals(Related, other.Related, StringComparison.OrdinalIgnoreCase);

    public override bool Equals(object? obj) => Equals(obj as TestProjectTopologyDebt);

    public override int GetHashCode()
    {
        var hash = new HashCode();
        hash.Add(Kind, StringComparer.Ordinal);
        hash.Add(Subject, StringComparer.OrdinalIgnoreCase);
        hash.Add(Related, StringComparer.OrdinalIgnoreCase);
        return hash.ToHashCode();
    }
}

internal sealed record TestProjectTopologyResult(
    bool IsAccepted,
    bool RequiresStrictReduction,
    ImmutableArray<TestProjectTopologyDebt> BaseDebt,
    ImmutableArray<TestProjectTopologyDebt> CandidateDebt,
    ImmutableArray<TestProjectTopologyDebt> IntroducedDebt,
    ImmutableArray<TestProjectTopologyDebt> RemovedDebt,
    string Message);

internal static partial class RepositoryRules
{
    internal const string DuplicateProductionIdentity = "duplicate-production-identity";
    internal const string MissingOwnedProject = "missing-owned-project";
    internal const string OrphanOwnedProject = "orphan-owned-project";
    internal const string MissingExpectedProductionReference =
        "missing-expected-production-reference";
    internal const string ExtraProductionReference = "extra-production-reference";
    internal const string OwnedTestToOwnedTestReference =
        "owned-test-to-owned-test-reference";

    // 横跨型 harness:测试仓库自身的结构或执行仓库脚本,横跨多个生产项目、
    // 不拥有其中任何一个,故不参与 `X` ↔ `X.Tests` 的拥有关系。
    //
    // 具名精确路径而非「凡不叫 X.Tests 者皆横跨」的命名规则 —— 后者会让任意
    // `*ArchitectureTests` / `*ScriptTests` 自动逃逸拥有关系检查,削弱
    // `OnlyExactCanonicalArchitectureHarnessPathIsExcluded` 有意钉住的守卫:
    // 第三个**未具名**的横跨项目仍须判 orphan-owned-project。加一条具名路径是
    // 保守扩展(旧判 admit 者仍 admit),换成命名规则则是放宽。
    internal static readonly ImmutableHashSet<string> CrossCuttingHarnessPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj");

    private static readonly Uri RepositoryUri = new("https://repository.invalid/");

    // Boundary: runnable identity stays a runtime concern. Static detection would reimplement C#
    // attributes, MSBuild Compile evaluation, and preprocessor symbols. Full-suite TRX verification
    // consumes the owner assemblies derived here and requires nonzero executed identity for each.
    internal static TestProjectTopologySnapshot ReadTrackedProjects(string repositoryRoot)
    {
        ArgumentNullException.ThrowIfNull(repositoryRoot);

        var projects = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.EndsWith(
                ".csproj",
                StringComparison.Ordinal))
            .Select(file => new TestProjectTopologyProject(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        return new TestProjectTopologySnapshot(projects);
    }

    internal static TestProjectTopologySnapshot ReadSnapshotProjects(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);

        var projects = snapshot.Files.Values
            .Where(static file => file.Path.Value.EndsWith(
                ".csproj",
                StringComparison.Ordinal))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .Select(file => new TestProjectTopologyProject(
                file.Path.Value,
                file.Text))
            .ToArray();
        return new TestProjectTopologySnapshot(projects);
    }

    internal static TestProjectTopologyResult EvaluateSnapshots(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);

        return Evaluate(
            ReadSnapshotProjects(protectedBase),
            ReadSnapshotProjects(candidate));
    }

    internal static TestProjectTopologyResult Evaluate(
        TestProjectTopologySnapshot protectedBase,
        TestProjectTopologySnapshot candidate)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);

        var baseGraph = BuildDebtGraph(protectedBase);
        var candidateGraph = BuildDebtGraph(candidate);
        var baseDebt = baseGraph.Debt.ToHashSet();
        var candidateDebt = candidateGraph.Debt.ToHashSet();
        var introduced = Sort(candidateDebt.Except(baseDebt));
        var removed = Sort(baseDebt.Except(candidateDebt));
        var requiresStrictReduction = TouchesBaseDebtVertex(
                protectedBase,
                candidate,
                baseGraph)
            || CreatesMissingOwnedProject(baseGraph, candidateGraph);

        // This set containment is the delta ratchet. A count comparison would admit an
        // equal-sized exchange of inherited debt for a new violation identity.
        var candidateDebtIsContained = candidateDebt.IsSubsetOf(baseDebt);
        var strictReductionSatisfied = !requiresStrictReduction
            || candidateDebt.IsProperSubsetOf(baseDebt);
        var accepted = candidateDebtIsContained && strictReductionSatisfied;
        var message = accepted
            ? requiresStrictReduction
                ? $"candidate debt strictly contracts from {baseDebt.Count} to {candidateDebt.Count}"
                : $"candidate debt remains within the {baseDebt.Count}-identity protected-base set"
            : !candidateDebtIsContained
                ? $"candidate introduces topology debt: {Format(introduced)}"
                : "candidate touches inherited topology debt without strictly reducing it";

        return new TestProjectTopologyResult(
            accepted,
            requiresStrictReduction,
            baseGraph.Debt,
            candidateGraph.Debt,
            introduced,
            removed,
            message);
    }

    internal static ImmutableArray<TestProjectTopologyDebt> CalculateDebt(
        TestProjectTopologySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        return BuildDebtGraph(snapshot).Debt;
    }

    internal static ImmutableArray<string> CalculateOwnerAssemblies(
        TestProjectTopologySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        return BuildDebtGraph(snapshot).OwnedTestProjects
            .Select(static project => project.AssemblyName)
            .Distinct(StringComparer.OrdinalIgnoreCase)
            .Order(StringComparer.OrdinalIgnoreCase)
            .ToImmutableArray();
    }

    private static DebtGraph BuildDebtGraph(TestProjectTopologySnapshot snapshot)
    {
        var allProjects = snapshot.Projects
            .Select(ParseProject)
            .OrderBy(static project => project.Path, StringComparer.Ordinal)
            .ToArray();
        var projectByPath = allProjects.ToDictionary(
            static project => project.Path,
            StringComparer.Ordinal);
        var productionProjects = allProjects
            .Where(static project => project.IsProduction)
            .ToArray();
        var ownedTestProjects = allProjects
            .Where(static project => project.IsOwnedTest)
            .ToArray();
        var productionByIdentity = productionProjects
            .GroupBy(static project => project.AssemblyName, StringComparer.OrdinalIgnoreCase)
            .ToDictionary(
                static group => group.Key,
                static group => group.ToArray(),
                StringComparer.OrdinalIgnoreCase);
        var ownedTestsByIdentity = ownedTestProjects
            .GroupBy(static project => project.AssemblyName, StringComparer.OrdinalIgnoreCase)
            .ToDictionary(
                static group => group.Key,
                static group => group.ToArray(),
                StringComparer.OrdinalIgnoreCase);
        var productionByPath = productionProjects.ToDictionary(
            static project => project.Path,
            StringComparer.Ordinal);
        var ownedTestByPath = ownedTestProjects.ToDictionary(
            static project => project.Path,
            StringComparer.Ordinal);
        var participants = new Dictionary<TestProjectTopologyDebt, HashSet<string>>();

        foreach (var group in productionByIdentity.Values.Where(static group => group.Length > 1))
        {
            AddDebt(
                participants,
                new TestProjectTopologyDebt(
                    DuplicateProductionIdentity,
                    group[0].AssemblyName,
                    group[0].AssemblyName),
                group.Select(static project => project.Path));
        }

        foreach (var group in productionByIdentity.Values)
        {
            var productionIdentity = group[0].AssemblyName;
            var expectedTestIdentity = productionIdentity + ".Tests";
            var matchingOwnedTests = ownedTestsByIdentity.TryGetValue(
                    expectedTestIdentity,
                    out var tests)
                ? tests
                : [];

            if (matchingOwnedTests.Length != 1)
            {
                AddDebt(
                    participants,
                    new TestProjectTopologyDebt(
                        MissingOwnedProject,
                        productionIdentity,
                        expectedTestIdentity),
                    group.Select(static project => project.Path)
                        .Concat(matchingOwnedTests.Select(static project => project.Path)));
            }
        }

        foreach (var test in ownedTestProjects)
        {
            var expectedProductionIdentity = test.AssemblyName.EndsWith(
                    ".Tests",
                    StringComparison.OrdinalIgnoreCase)
                ? test.AssemblyName[..^".Tests".Length]
                : string.Empty;
            var matchingProduction = expectedProductionIdentity.Length > 0
                && productionByIdentity.TryGetValue(expectedProductionIdentity, out var projects)
                    ? projects
                    : [];
            if (matchingProduction.Length != 1)
            {
                AddDebt(
                    participants,
                    new TestProjectTopologyDebt(
                        OrphanOwnedProject,
                        test.AssemblyName,
                        expectedProductionIdentity),
                    [test.Path, .. matchingProduction.Select(static project => project.Path)]);
            }

            var directProductionReferences = test.DirectProjectReferences
                .Where(productionByPath.ContainsKey)
                .Select(reference => productionByPath[reference])
                .DistinctBy(static project => project.Path)
                .ToArray();
            if (matchingProduction.Length == 1
                && directProductionReferences.All(project => project.Path != matchingProduction[0].Path))
            {
                AddDebt(
                    participants,
                    new TestProjectTopologyDebt(
                        MissingExpectedProductionReference,
                        test.AssemblyName,
                        matchingProduction[0].AssemblyName),
                    [test.Path, matchingProduction[0].Path]);
            }

            foreach (var extra in directProductionReferences.Where(project =>
                         matchingProduction.Length != 1
                         || project.Path != matchingProduction[0].Path))
            {
                AddDebt(
                    participants,
                    new TestProjectTopologyDebt(
                        ExtraProductionReference,
                        test.AssemblyName,
                        extra.AssemblyName),
                    [test.Path, extra.Path]);
            }

            foreach (var reference in test.DirectProjectReferences
                         .Where(ownedTestByPath.ContainsKey)
                         .Select(reference => ownedTestByPath[reference])
                         .DistinctBy(static project => project.Path))
            {
                AddDebt(
                    participants,
                    new TestProjectTopologyDebt(
                        OwnedTestToOwnedTestReference,
                        test.AssemblyName,
                        reference.AssemblyName),
                    [test.Path, reference.Path]);
            }
        }

        return new DebtGraph(
            Sort(participants.Keys),
            participants.ToDictionary(
                static pair => pair.Key,
                static pair => (IReadOnlySet<string>)pair.Value),
            projectByPath,
            ownedTestProjects);
    }

    private static ProjectVertex ParseProject(TestProjectTopologyProject project)
    {
        var path = NormalizePath(project.Path);
        var document = XDocument.Parse(project.Content, LoadOptions.None);
        var assemblyName = document.Descendants()
            .FirstOrDefault(static element => element.Name.LocalName == "AssemblyName")
            ?.Value.Trim();
        if (string.IsNullOrEmpty(assemblyName))
        {
            assemblyName = System.IO.Path.GetFileNameWithoutExtension(path);
        }

        var directReferences = document.Descendants()
            .Where(static element => element.Name.LocalName == "ProjectReference")
            .Select(static element => (string?)element.Attribute("Include"))
            .Where(static include => !string.IsNullOrWhiteSpace(include))
            .Select(include => ResolveProjectReference(path, include!))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var isXunit = HasLiteralXunitReference(project.Content);

        return new ProjectVertex(
            path,
            project.Content,
            assemblyName,
            IsProductionProject(path),
            IsOwnedTestProject(path, isXunit),
            directReferences);
    }

    private static bool IsProductionProject(string path)
    {
        var parts = path.Split('/');
        return parts.Length == 3
            && parts[0] == "tools"
            && parts[1] != "tests"
            && parts[2].EndsWith(".csproj", StringComparison.Ordinal);
    }

    private static bool IsOwnedTestProject(string path, bool isXunit) =>
        isXunit
        && path.StartsWith("tools/tests/", StringComparison.Ordinal)
        && path.EndsWith(".csproj", StringComparison.Ordinal)
        && !CrossCuttingHarnessPaths.Contains(path);

    private static string ResolveProjectReference(string projectPath, string include)
    {
        var slash = projectPath.LastIndexOf('/');
        var directory = slash < 0 ? string.Empty : projectPath[..(slash + 1)];
        var directoryUri = new Uri(RepositoryUri, directory);
        var referenceUri = new Uri(directoryUri, include.Replace('\\', '/'));
        return Uri.UnescapeDataString(referenceUri.AbsolutePath.TrimStart('/'));
    }

    private static string NormalizePath(string path) => path.Replace('\\', '/');

    private static bool TouchesBaseDebtVertex(
        TestProjectTopologySnapshot protectedBase,
        TestProjectTopologySnapshot candidate,
        DebtGraph baseGraph)
    {
        var baseProjects = protectedBase.Projects.ToDictionary(
            project => NormalizePath(project.Path),
            StringComparer.Ordinal);
        var candidateProjects = candidate.Projects.ToDictionary(
            project => NormalizePath(project.Path),
            StringComparer.Ordinal);
        var changedProjectPaths = baseProjects.Keys
            .Union(candidateProjects.Keys, StringComparer.Ordinal)
            .Where(path => !baseProjects.TryGetValue(path, out var before)
                || !candidateProjects.TryGetValue(path, out var after)
                || !string.Equals(before.Content, after.Content, StringComparison.Ordinal))
            .ToHashSet(StringComparer.Ordinal);

        return baseGraph.Participants.Values.Any(paths => paths.Overlaps(changedProjectPaths));
    }

    private static bool CreatesMissingOwnedProject(DebtGraph baseGraph, DebtGraph candidateGraph)
    {
        var missingIdentities = baseGraph.Debt
            .Where(static debt => debt.Kind == MissingOwnedProject)
            .Select(static debt => debt.Related)
            .ToHashSet(StringComparer.OrdinalIgnoreCase);
        return candidateGraph.OwnedTestProjects.Any(candidate =>
            missingIdentities.Contains(candidate.AssemblyName)
            && !baseGraph.OwnedTestProjects.Any(existing =>
                existing.Path == candidate.Path
                && StringComparer.OrdinalIgnoreCase.Equals(
                    existing.AssemblyName,
                    candidate.AssemblyName)));
    }

    private static bool HasLiteralXunitReference(string content)
    {
        var document = XDocument.Parse(content, LoadOptions.None);
        return document.Descendants().Any(static element =>
            element.Name.LocalName == "PackageReference"
            && string.Equals(
                (string?)element.Attribute("Include"),
                "xunit",
                StringComparison.Ordinal));
    }

    private static void AddDebt(
        IDictionary<TestProjectTopologyDebt, HashSet<string>> participants,
        TestProjectTopologyDebt debt,
        IEnumerable<string> paths)
    {
        if (!participants.TryGetValue(debt, out var debtParticipants))
        {
            debtParticipants = new HashSet<string>(StringComparer.Ordinal);
            participants.Add(debt, debtParticipants);
        }

        debtParticipants.UnionWith(paths);
    }

    private static ImmutableArray<TestProjectTopologyDebt> Sort(
        IEnumerable<TestProjectTopologyDebt> debt) => debt
        .OrderBy(static item => item.Kind, StringComparer.Ordinal)
        .ThenBy(static item => item.Subject, StringComparer.Ordinal)
        .ThenBy(static item => item.Related, StringComparer.Ordinal)
        .ToImmutableArray();

    private static string Format(IReadOnlyList<TestProjectTopologyDebt> debt) => debt.Count == 0
        ? "none"
        : string.Join(
            ", ",
            debt.Select(static item => $"{item.Kind} {item.Subject} -> {item.Related}"));

    private sealed record ProjectVertex(
        string Path,
        string Content,
        string AssemblyName,
        bool IsProduction,
        bool IsOwnedTest,
        ImmutableArray<string> DirectProjectReferences);

    private sealed record DebtGraph(
        ImmutableArray<TestProjectTopologyDebt> Debt,
        IReadOnlyDictionary<TestProjectTopologyDebt, IReadOnlySet<string>> Participants,
        IReadOnlyDictionary<string, ProjectVertex> ProjectByPath,
        IReadOnlyList<ProjectVertex> OwnedTestProjects);
}
