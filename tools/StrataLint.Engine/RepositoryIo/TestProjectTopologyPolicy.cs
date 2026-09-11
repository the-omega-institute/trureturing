using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record TestProjectTopologyProject(
    string Path,
    string Content,
    EngineeringProjectRegistration Registration);

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

    internal static TestProjectTopologySnapshot ReadTrackedProjects(string repositoryRoot)
    {
        var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => file.RelativePath == EngineeringProjectRegistry.ManifestPath
                || file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => new EngineeringSource(file.RelativePath, File.ReadAllText(file.FullPath))).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        var byPath = files.ToDictionary(file => file.Path, StringComparer.Ordinal);
        return new TestProjectTopologySnapshot(registry.Projects.Select(project =>
            new TestProjectTopologyProject(project.Path, byPath[project.Path].Content, project)).ToArray());
    }

    internal static TestProjectTopologySnapshot ReadSnapshotProjects(RepositorySnapshot snapshot) =>
        ReadRegisteredProjects(snapshot, EngineeringProjectRegistry.Read(snapshot));

    internal static TestProjectTopologySnapshot ReadBaseProjects(RepositorySnapshot baseline, RepositorySnapshot candidate) =>
        ReadRegisteredProjects(baseline, EngineeringProjectRegistry.ReadBase(baseline, candidate));

    private static TestProjectTopologySnapshot ReadRegisteredProjects(RepositorySnapshot snapshot, EngineeringProjectRegistry registry) =>
        new(registry.Projects.Select(project => new TestProjectTopologyProject(project.Path,
            snapshot.Files[RepoPath.CreateKnown(project.Path)].Text, project)).ToArray());

    internal static TestProjectTopologyResult EvaluateSnapshots(RepositorySnapshot protectedBase, RepositorySnapshot candidate) =>
        Evaluate(ReadBaseProjects(protectedBase, candidate), ReadSnapshotProjects(candidate));

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
            .Select(RegisteredVertex)
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
            var expectedTestIdentity = group[0].Registration.OwnedTestAssembly!;
            var matchingOwnedTests = ownedTestProjects.Where(test =>
                group.Any(production => test.Registration.Owner!.Path == production.Path)
                && StringComparer.OrdinalIgnoreCase.Equals(test.AssemblyName, expectedTestIdentity)).ToArray();

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
            var owner = test.Registration.Owner!;
            var expectedProductionIdentity = owner.Assembly;
            var matchingProduction = productionProjects.Where(project => project.Path == owner.Path
                && StringComparer.OrdinalIgnoreCase.Equals(project.AssemblyName, owner.Assembly)).ToArray();
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

    private static ProjectVertex RegisteredVertex(TestProjectTopologyProject project) => new(
        project.Path,
        project.Registration.Assembly,
        project.Registration.Role == "production",
        project.Registration.IsTest,
        project.Registration.Role == "owned-test",
        project.Registration.References.ToImmutableArray(),
        project.Registration);

    private static bool TouchesBaseDebtVertex(
        TestProjectTopologySnapshot protectedBase,
        TestProjectTopologySnapshot candidate,
        DebtGraph baseGraph)
    {
        var baseProjects = protectedBase.Projects.ToDictionary(
            project => project.Path,
            StringComparer.Ordinal);
        var candidateProjects = candidate.Projects.ToDictionary(
            project => project.Path,
            StringComparer.Ordinal);
        var changedProjectPaths = baseProjects.Keys
            .Union(candidateProjects.Keys, StringComparer.Ordinal)
            .Where(path => !baseProjects.TryGetValue(path, out var before)
                || !candidateProjects.TryGetValue(path, out var after)
                || !string.Equals(before.Content, after.Content, StringComparison.Ordinal)
                || !SameTopologyRegistration(before.Registration, after.Registration))
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

    private static bool SameTopologyRegistration(EngineeringProjectRegistration before, EngineeringProjectRegistration after) =>
        before.Assembly == after.Assembly && before.Role == after.Role && before.Owner == after.Owner
        && before.OwnedTestAssembly == after.OwnedTestAssembly && before.References.SequenceEqual(after.References);

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
        string AssemblyName,
        bool IsProduction,
        bool IsTest,
        bool IsOwnedTest,
        ImmutableArray<string> DirectProjectReferences,
        EngineeringProjectRegistration Registration);

    private sealed record DebtGraph(
        ImmutableArray<TestProjectTopologyDebt> Debt,
        IReadOnlyDictionary<TestProjectTopologyDebt, IReadOnlySet<string>> Participants,
        IReadOnlyDictionary<string, ProjectVertex> ProjectByPath,
        IReadOnlyList<ProjectVertex> OwnedTestProjects);
}
