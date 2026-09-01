using System.Collections.Immutable;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }

internal enum EngineeringSelectedTestReason { BaseBaseline, UnknownInput, DeclaredInput }

internal sealed record EngineeringSelectedTest(
    string ProjectPath,
    string Id,
    EngineeringSelectedTestReason Reason,
    string Detail,
    string Assembly = "");

internal sealed record EngineeringTestPlan(
    EngineeringTestPlanKind Kind,
    ImmutableArray<string> ChangedPaths,
    ImmutableArray<EngineeringSelectedTest> Tests,
    string Reason);

internal sealed record EngineeringTestInvocation(
    string Target,
    string? Filter,
    ImmutableArray<EngineeringSelectedTest> ExpectedTests);

internal static class EngineeringTestPlanDeriver
{
    internal static EngineeringTestPlan DeriveRepository(
        string repositoryRoot,
        IReadOnlyList<string> changedPaths)
    {
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        return EngineeringTestPlanPolicy.Evaluate(changedPaths, map);
    }

    internal static EngineeringTestPlan DeriveSnapshot(
        RepositorySnapshot snapshot,
        IReadOnlyList<string> changedPaths,
        bool full = false)
    {
        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);
        EnsureClosedMap(map);
        var assemblies = AssemblyByProject(snapshot, map);
        if (full)
        {
            return EngineeringTestPlanPolicy.Full(
                changedPaths,
                EngineeringTestPlanPolicy.WithMetadataReceipt(
                    "FULL=1 requests the diagnostic full plan",
                    map),
                EngineeringTestPlanPolicy.BaseTests(map, assemblies));
        }

        return EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            map,
            assemblyByProject: assemblies);
    }

    internal static ImmutableArray<(string Assembly, string Id)> DeriveSourceIdentities(
        RepositorySnapshot snapshot)
    {
        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);
        EnsureClosedMap(map);
        return EngineeringTestPlanPolicy.SourceIdentities(
            map,
            AssemblyByProject(snapshot, map));
    }

    private static void EnsureClosedMap(ScribeTestMap map)
    {
        var failures = map.UnclassifiedManagedProjectPaths
            .Concat(map.OrphanManagedSourcePaths)
            .Concat(map.CompileQueryFindings.Select(static finding => finding.Path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (failures.Length != 0)
        {
            throw new InvalidOperationException(
                $"base test identity attribution failed: {string.Join(", ", failures)}");
        }
    }

    private static IReadOnlyDictionary<string, string> AssemblyByProject(
        RepositorySnapshot snapshot,
        ScribeTestMap map)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var project in map.Methods
                     .Select(method => map.CompileProjectBySourcePath.TryGetValue(method.SourcePath, out var owner)
                         ? owner
                         : throw new InvalidOperationException(
                             $"project attribution failed for {method.Identity}"))
                     .Distinct(StringComparer.Ordinal))
        {
            if (!snapshot.TryGetFile(project, out var file))
            {
                throw new InvalidOperationException($"base test project is absent: {project}");
            }

            var document = XDocument.Parse(file.Text, LoadOptions.None);
            var assembly = document.Descendants()
                .FirstOrDefault(static element => element.Name.LocalName == "AssemblyName")?.Value
                ?? Path.GetFileNameWithoutExtension(project);
            if (string.IsNullOrWhiteSpace(assembly) || assembly.Contains("$(", StringComparison.Ordinal))
            {
                throw new InvalidOperationException(
                    $"base test project has no static assembly identity: {project}");
            }

            result.Add(project, assembly);
        }

        return result;
    }
}

internal static class EngineeringTestPlanPolicy
{
    internal static EngineeringTestPlan Evaluate(
        IReadOnlyList<string> changedPaths,
        ScribeTestMap map,
        IReadOnlyDictionary<string, string>? assemblyByProject = null)
    {
        var changed = changedPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
        if (changed.Any(IsFullSurface))
        {
            return Full(
                changed,
                WithMetadataReceipt(
                    "candidate delta changes the engineering implementation or a repository-root build input",
                    map),
                BaseTests(map, assemblyByProject));
        }

        var failures = map.UnclassifiedManagedProjectPaths
            .Concat(map.OrphanManagedSourcePaths)
            .Concat(map.DanglingCompileFailProofProjectExemptionPaths)
            .Concat(map.CompileQueryFindings.Select(static finding => finding.Path))
            .ToArray();
        if (failures.Length != 0)
        {
            var detail = string.Join(", ", failures.Order(StringComparer.Ordinal));
            return Full(changed, WithMetadataReceipt($"project attribution failed: {detail}", map));
        }

        var runnableMethods = RunnableMethods(map).ToArray();
        var emptyDegradations = map.MetadataDegradations.Where(degradation =>
            !runnableMethods.Any(method =>
                map.CompileProjectBySourcePath.TryGetValue(method.SourcePath, out var project)
                && project == degradation.ProjectPath)).ToArray();
        if (emptyDegradations.Length != 0)
        {
            return Full(
                changed,
                WithMetadataReceipt(
                    "metadata degradation left a test project with no recognized identities; running the full suite",
                    map),
                BaseTests(map, assemblyByProject));
        }

        var degradationByProject = map.MetadataDegradations.ToDictionary(
            static degradation => degradation.ProjectPath,
            StringComparer.Ordinal);
        var tests = new List<EngineeringSelectedTest>();
        foreach (var method in runnableMethods)
        {
            if (!map.CompileProjectBySourcePath.TryGetValue(method.SourcePath, out var project))
            {
                return Full(changed, $"project attribution failed for {method.Identity}");
            }

            EngineeringSelectedTestReason? reason = null;
            string? detail = null;
            var matched = changed.FirstOrDefault(path => method.Paths.Any(input => Covers(input, path)));
            if (matched is not null)
            {
                reason = EngineeringSelectedTestReason.DeclaredInput;
                detail = $"changed path {matched} intersects a declared repository input";
            }
            else if (changed.FirstOrDefault(path =>
                         method.CompileTimeInputUniverses.Any(universe => universe.Covers(path)))
                     is { } compileTimeInput)
            {
                reason = EngineeringSelectedTestReason.DeclaredInput;
                detail = $"changed path {compileTimeInput} intersects a compile-time input universe";
            }
            else if (method.IsUnknown)
            {
                reason = EngineeringSelectedTestReason.UnknownInput;
                detail = degradationByProject.TryGetValue(project, out var degradation)
                    ? $"metadata unavailable for {project}; every test in the project is "
                        + $"conservatively unknown: {degradation.Reason}"
                    : "target has repository inputs that are not statically closed";
            }

            if (reason is not null)
            {
                tests.Add(new EngineeringSelectedTest(
                    project,
                    method.Id,
                    reason.Value,
                    detail!,
                    Assembly(project, assemblyByProject)));
            }
        }

        var selected = tests
            .DistinctBy(static test => (test.ProjectPath, test.Id))
            .OrderBy(static test => test.ProjectPath, StringComparer.Ordinal)
            .ThenBy(static test => test.Id, StringComparer.Ordinal)
            .ToImmutableArray();
        return selected.Length == 0
            ? new EngineeringTestPlan(
                EngineeringTestPlanKind.None,
                changed,
                [],
                "candidate delta has no affected or locally conservative test target")
            : new EngineeringTestPlan(
                EngineeringTestPlanKind.Selected,
                changed,
                selected,
                WithMetadataReceipt(
                    $"selected {selected.Length} affected or locally conservative test targets",
                    map));
    }

    internal static ImmutableArray<EngineeringSelectedTest> BaseTests(
        ScribeTestMap map,
        IReadOnlyDictionary<string, string>? assemblyByProject) => RunnableMethods(map)
        .Select(method => map.CompileProjectBySourcePath.TryGetValue(method.SourcePath, out var project)
            ? new EngineeringSelectedTest(
                project,
                method.Id,
                EngineeringSelectedTestReason.BaseBaseline,
                map.MetadataDegradations.FirstOrDefault(degradation =>
                    degradation.ProjectPath == project) is { } degradation
                    ? $"metadata unavailable for {project}; every test in the project is "
                        + $"conservatively unknown: {degradation.Reason}"
                    : "identity is owned by the protected base",
                Assembly(project, assemblyByProject))
            : throw new InvalidOperationException($"project attribution failed for {method.Identity}"))
        .DistinctBy(static test => (test.Assembly, test.Id))
        .OrderBy(static test => test.Assembly, StringComparer.Ordinal)
        .ThenBy(static test => test.Id, StringComparer.Ordinal)
        .ToImmutableArray();

    internal static string WithMetadataReceipt(string reason, ScribeTestMap map) =>
        map.MetadataDegradations.Count == 0
            ? reason
            : reason + "; " + string.Join("; ", map.MetadataDegradations
                .OrderBy(static degradation => degradation.ProjectPath, StringComparer.Ordinal)
                .ThenBy(static degradation => degradation.Reason, StringComparer.Ordinal)
                .Select(static degradation =>
                $"metadata degraded for {degradation.ProjectPath}: {degradation.Reason}"));
    internal static ImmutableArray<(string Assembly, string Id)> SourceIdentities(
        ScribeTestMap map,
        IReadOnlyDictionary<string, string> assemblyByProject) => map.Methods
        .Select(method =>
        {
            if (!map.CompileProjectBySourcePath.TryGetValue(method.SourcePath, out var project))
                throw new InvalidOperationException($"project attribution failed for {method.Identity}");
            if (!assemblyByProject.TryGetValue(project, out var assembly))
                throw new InvalidOperationException($"assembly attribution failed for {project}");
            return (Assembly: assembly, method.Id);
        })
        .OrderBy(static test => test.Assembly, StringComparer.OrdinalIgnoreCase)
        .ThenBy(static test => test.Id, StringComparer.Ordinal)
        .ToImmutableArray();

    private static IEnumerable<ScribeTestMethod> RunnableMethods(ScribeTestMap map) =>
        map.Methods.Where(static method =>
            !method.IsStaticallySkipped && !method.IsDiscoveryConditional);

    internal static EngineeringTestPlan Full(
        IReadOnlyList<string> changedPaths,
        string reason,
        ImmutableArray<EngineeringSelectedTest> tests = default) => new(
        EngineeringTestPlanKind.Full,
        changedPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
        tests.IsDefault ? [] : tests,
        reason);

    private static string Assembly(
        string project,
        IReadOnlyDictionary<string, string>? assemblyByProject) =>
        assemblyByProject is not null && assemblyByProject.TryGetValue(project, out var assembly)
            ? assembly
            : Path.GetFileNameWithoutExtension(project);

    // 仓根**文档**不是构建输入。上面那句 reason 自称 "a repository-root build input",
    // 而此谓词此前判的是任何仓根文件,比它自己声明的契约更宽 —— 收窄是对齐契约,不是削弱。
    //
    // 检测不降级(2026-08-30 实测三条):①全仓无任何测试读这三个文件的**内容**
    // (只当 root marker 与合成夹具字面量);②「本次改动把某工件顶过 800 行」由 admission 的
    // SL-003 delta 分支无条件 Block(RepositoryRules.Structure.cs),与 engineering 计划无关;
    // ③dev push 恒为 FULL,全仓容量巡检在合入后照跑。故一个文档 PR 自己能造成的违规,
    // 仍然逐条有机器拦得住;它此前连坐的是 3101 个与它无关的测试(实测 774s/次)。
    //
    // 名单是**排除式白名单**:不在其中的仓根文件一律仍判 full surface,
    // 故新增一个未分类的仓根文件 fail-closed。
    private static readonly ImmutableHashSet<string> RepositoryRootDocuments =
        ImmutableHashSet.Create(StringComparer.Ordinal, "AGENTS.md", "CLAUDE.md", "README.md");

    private static bool IsFullSurface(string path) =>
        path == "tools"
        || path.StartsWith("tools/", StringComparison.Ordinal)
        || (!path.Contains('/') && !RepositoryRootDocuments.Contains(path));

    private static bool Covers(string root, string path) =>
        path == root || path.StartsWith(root + "/", StringComparison.Ordinal);
}

internal static class EngineeringTestExecutor
{
    internal static int Execute(
        EngineeringTestPlan plan,
        Func<EngineeringTestInvocation, int> run)
    {
        if (plan.Kind == EngineeringTestPlanKind.None)
        {
            return 0;
        }

        if (plan.Kind == EngineeringTestPlanKind.Full)
            return run(new EngineeringTestInvocation("tools/StrataLint.sln", null, plan.Tests));

        var filter = string.Join('|', plan.Tests.Select(static test => $"FullyQualifiedName~{test.Id}").Distinct(StringComparer.Ordinal));
        try
        {
            if (run(new EngineeringTestInvocation("tools/StrataLint.sln", filter, plan.Tests)) == 0) return 0;
        }
        catch (Exception) { }
        return run(new EngineeringTestInvocation("tools/StrataLint.sln", null, plan.Tests));
    }
}
