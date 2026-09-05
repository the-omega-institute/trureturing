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

    // 共享测试支持项目:不含 xUnit、不被任何 `X.Tests` 拥有、也不拥有任何生产项目,
    // 故不参与 `X` ↔ `X.Tests` 的拥有关系,亦不计入受管测试项目的 `ProdRefs`。
    //
    // 与 CrossCuttingHarnessPaths 同形:**具名精确路径**,不是
    // `tools/TestSupport/<x>/<x>.csproj` 这样的目录文法 —— 后者会让任意新建的
    // 嵌套项目自动取得豁免身份,而具名一条是保守扩展。相应地,
    // NestedProjectOutsideTestsIsProductionAndNeedsItsOwnedDual 钉住:
    // 第二个**未具名**的嵌套项目仍按生产项目判,须有其对偶测试项目。
    //
    // 案由(第 20″ 条):该项目 2026-08-30 曾以 tools/tests/ 下的路径被具名进
    // CrossCuttingHarnessPaths(dbaef43a43),其后条目被删(4288ac913c)、项目于
    // 2026-09-02 迁至 tools/TestSupport/(6f4cb2d501)。迁移后路径为四段,而彼时
    // IsProductionProject 要求恰三段 ⟹ 该节点与其全部入边静默脱离债务代数。
    // 2026-09-05 实测:向它新增三条入边(PR #5324)产生零拓扑债。
    internal const string TestSupportProjectPath =
        "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj";

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
        var testProjects = allProjects
            .Where(static project => project.IsTest)
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
        var testByPath = testProjects.ToDictionary(
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

        }

        // 主语与宾语都取全部受管测试项目,不取 ownedTestProjects:横跨型 harness 的豁免
        // 论证的是拥有关系,与「该不该依赖另一个测试项目」正交(#5419)。**两侧都换** ——
        // 只扩主语会留下「引用一个横跨型 harness」的同形缺口(当前无人这么写,故缺口空转,
        // 但它与被扩的那一侧是同一个错误类)。本循环此前嵌在上面的 ownedTestProjects
        // 循环内部,故必须整体提出来,否则换的只是过滤器而不是主语面。
        foreach (var test in testProjects)
        {
            foreach (var reference in test.DirectProjectReferences
                         .Where(testByPath.ContainsKey)
                         .Select(reference => testByPath[reference])
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
            IsTestProject(path, isXunit),
            IsOwnedTestProject(path, isXunit),
            directReferences);
    }

    // 作用域是 tools/ 下、tests/ 之外的**任意深度** csproj:早先的「恰三段」写法
    // 让多嵌一层的项目整个逃出双射与引用债务计算。
    private static bool IsProductionProject(string path) =>
        path.StartsWith("tools/", StringComparison.Ordinal)
        && !path.StartsWith("tools/tests/", StringComparison.Ordinal)
        && path.EndsWith(".csproj", StringComparison.Ordinal)
        && !string.Equals(path, TestSupportProjectPath, StringComparison.Ordinal);

    // 「是不是受管测试项目」与「是不是拥有某个生产项目」是两个正交的问题,此前由同一个
    // 谓词回答,于是 CrossCuttingHarnessPaths 对**拥有关系**的豁免被一并施加到
    // test→test 依赖上,使 ArchitectureTests / ScriptTests 的四条 test→test 边
    // 结构上不进债账(#5419)。IsOwnedTestProject 由 IsTestProject **收窄**而来,
    // 而非并列另写一个谓词 —— 这样「旧判 owned 者仍 owned」在结构上成立(保守扩展),
    // 不依赖测试来保证。
    private static bool IsTestProject(string path, bool isXunit) =>
        isXunit
        && path.StartsWith("tools/tests/", StringComparison.Ordinal)
        && path.EndsWith(".csproj", StringComparison.Ordinal);

    private static bool IsOwnedTestProject(string path, bool isXunit) =>
        IsTestProject(path, isXunit)
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

        // test→test 债的参与者**不**计入路径级触发:该债的性质是一条 ProjectReference 关系,
        // 而改同一个 csproj 里的 PackageReference 版本或任何无关属性并没有碰那条关系。
        // 若计入,则「改这五个 csproj 之一」的每个 PR 都必须当场删掉一条 test→test 边 ——
        // 实测近 7 天这五个文件共被改 28 次(约 4 次/天),而可还的边总共只有 4 条,
        // 于是第五个这样的 PR 起合法候选集合为空(局部无解态),并诱发三类规避:
        // 夹带无关还债、复制助手以抢付一条债、或改用 ReferenceOutputAssembly=false 把边藏起来。
        //
        // 压力并未放松:新增第五条边仍由 candidateDebt ⊆ baseDebt 当场拒;
        // 等量换债(删一加一)同样因集合包含而非计数比较被拒;删边仍使债严格收缩。
        // 一个 csproj 若同时参与某个**拥有关系**债,仍由那条债触发严格减债。
        return baseGraph.Participants
            .Where(static entry => entry.Key.Kind != OwnedTestToOwnedTestReference)
            .Any(entry => entry.Value.Overlaps(changedProjectPaths));
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
        bool IsTest,
        bool IsOwnedTest,
        ImmutableArray<string> DirectProjectReferences);

    private sealed record DebtGraph(
        ImmutableArray<TestProjectTopologyDebt> Debt,
        IReadOnlyDictionary<TestProjectTopologyDebt, IReadOnlySet<string>> Participants,
        IReadOnlyDictionary<string, ProjectVertex> ProjectByPath,
        IReadOnlyList<ProjectVertex> OwnedTestProjects);
}
