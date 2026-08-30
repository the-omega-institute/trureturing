using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }

internal enum EngineeringSelectedTestReason { BaseBaseline, UnknownInput, DeclaredInput, CompiledInput }

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
        var compiled = EngineeringCompileInputDeriver.FindAffectedTestProjects(
            repositoryRoot,
            changedPaths,
            out var failure);
        return EngineeringTestPlanPolicy.Evaluate(changedPaths, map, compiled, failure);
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

        var compiled = EngineeringCompileInputDeriver.FindAffectedTestProjects(
            snapshot,
            changedPaths,
            out var failure);
        if (failure is not null)
        {
            throw new InvalidOperationException($"project attribution failed: {failure}");
        }

        return EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            map,
            compiled,
            assemblyByProject: assemblies);
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
        IReadOnlySet<string> compileAffectedTestProjects,
        string? attributionFailure = null,
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
        if (attributionFailure is not null || failures.Length != 0)
        {
            var detail = attributionFailure ?? string.Join(", ", failures.Order(StringComparer.Ordinal));
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
            if (compileAffectedTestProjects.Contains(project))
            {
                reason = EngineeringSelectedTestReason.CompiledInput;
                detail = "a changed path is a transitive compiled input of the test project";
            }
            else
            {
                var matched = changed.FirstOrDefault(path => method.Paths.Any(input => Covers(input, path)));
                if (matched is not null)
                {
                    reason = EngineeringSelectedTestReason.DeclaredInput;
                    detail = $"changed path {matched} intersects a declared repository input";
                }
                else if (method.IsUnknown)
                {
                    reason = EngineeringSelectedTestReason.UnknownInput;
                    detail = degradationByProject.TryGetValue(project, out var degradation)
                        ? $"metadata unavailable for {project}; every test in the project is "
                            + $"conservatively unknown: {degradation.Reason}"
                        : "target has repository inputs that are not statically closed";
                }
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

    private static IEnumerable<ScribeTestMethod> RunnableMethods(ScribeTestMap map) =>
        map.Methods.Where(static method => !method.IsStaticallySkipped);

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

internal static class EngineeringCompileInputDeriver
{
    private static readonly ImmutableHashSet<string> InputItemTypes =
        ImmutableHashSet.Create(StringComparer.Ordinal, "AdditionalFiles", "Compile", "Content", "EmbeddedResource", "None");

    internal static IReadOnlySet<string> FindAffectedTestProjects(
        string repositoryRoot,
        IReadOnlyList<string> changedPaths,
        out string? failure)
    {
        try
        {
            return FindAffectedTestProjects(
                GitIndexRepositoryFiles.Enumerate(repositoryRoot)
                .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
                .Select(file => (file.RelativePath, Content: File.ReadAllText(file.FullPath))),
                changedPaths,
                out failure);
        }
        catch (Exception exception) when (exception is FormatException or System.Xml.XmlException or IOException)
        {
            failure = exception.Message;
            return new HashSet<string>(StringComparer.Ordinal);
        }
    }

    internal static IReadOnlySet<string> FindAffectedTestProjects(
        RepositorySnapshot snapshot,
        IReadOnlyList<string> changedPaths,
        out string? failure)
    {
        try
        {
            return FindAffectedTestProjects(
                snapshot.Files.Values
                    .Where(static file => file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal))
                    .Select(static file => (file.Path.Value, Content: file.Text)),
                changedPaths,
                out failure);
        }
        catch (Exception exception) when (exception is FormatException or System.Xml.XmlException or IOException)
        {
            failure = exception.Message;
            return new HashSet<string>(StringComparer.Ordinal);
        }
    }

    private static IReadOnlySet<string> FindAffectedTestProjects(
        IEnumerable<(string Path, string Content)> projectFiles,
        IReadOnlyList<string> changedPaths,
        out string? failure)
    {
        try
        {
            var projects = projectFiles
                .Select(static file => ParseProject(file.Path, file.Content))
                .ToDictionary(static project => project.Path, StringComparer.Ordinal);
            var affected = projects.Values
                .Where(project => project.InputPatterns.Any(pattern => changedPaths.Any(path => EngineeringInputGlob.IsMatch(pattern, path))))
                .Select(static project => project.Path)
                .ToHashSet(StringComparer.Ordinal);
            var testProjects = projects.Values
                .Where(static project => project.IsTest)
                .Where(project => DependsOnAffected(project.Path, projects, affected, []))
                .Select(static project => project.Path)
                .ToHashSet(StringComparer.Ordinal);
            failure = null;
            return testProjects;
        }
        catch (Exception exception) when (exception is FormatException or System.Xml.XmlException or IOException)
        {
            failure = exception.Message;
            return new HashSet<string>(StringComparer.Ordinal);
        }
    }

    private static EngineeringProject ParseProject(string path, string content)
    {
        var document = XDocument.Parse(content, LoadOptions.None);
        var references = new List<string>();
        var inputs = new List<string>();
        foreach (var item in document.Descendants().Where(static element => element.Attribute("Include") is not null))
        {
            var include = (string)item.Attribute("Include")!;
            foreach (var value in include.Split(';', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
            {
                if (value.Contains("$(", StringComparison.Ordinal))
                {
                    throw new FormatException($"{path} has an unevaluated input: {value}");
                }

                var resolved = Resolve(path, value);
                if (item.Name.LocalName == "ProjectReference")
                {
                    references.Add(resolved);
                }
                else if (InputItemTypes.Contains(item.Name.LocalName) && !resolved.StartsWith("tools/", StringComparison.Ordinal))
                {
                    EngineeringInputGlob.Validate(resolved);
                    inputs.Add(resolved);
                }
            }
        }

        return new EngineeringProject(
            path,
            document.Descendants().Any(static element =>
                element.Name.LocalName == "PackageReference"
                && string.Equals((string?)element.Attribute("Include"), "xunit", StringComparison.OrdinalIgnoreCase)),
            references,
            inputs);
    }

    private static bool DependsOnAffected(
        string path,
        IReadOnlyDictionary<string, EngineeringProject> projects,
        IReadOnlySet<string> affected,
        HashSet<string> visited)
    {
        if (!visited.Add(path)) return false;
        if (affected.Contains(path)) return true;
        return projects.TryGetValue(path, out var project)
            && project.References.Any(reference => DependsOnAffected(reference, projects, affected, visited));
    }

    private static string Resolve(string projectPath, string include)
    {
        var segments = new List<string>();
        foreach (var segment in projectPath.Split('/').SkipLast(1).Concat(include.Replace('\\', '/').Split('/')))
        {
            if (segment is "" or ".") continue;
            if (segment == "..")
            {
                if (segments.Count == 0) throw new FormatException($"{projectPath} has an input outside the repository: {include}");
                segments.RemoveAt(segments.Count - 1);
            }
            else
            {
                segments.Add(segment);
            }
        }

        return string.Join('/', segments);
    }

    private sealed record EngineeringProject(
        string Path,
        bool IsTest,
        IReadOnlyList<string> References,
        IReadOnlyList<string> InputPatterns);
}

internal static class EngineeringInputGlob
{
    internal static void Validate(string pattern) => _ = CreateRegex(pattern);

    internal static bool IsMatch(string pattern, string path) => CreateRegex(pattern).IsMatch(path);

    private static Regex CreateRegex(string pattern)
    {
        if (string.IsNullOrWhiteSpace(pattern)
            || pattern[0] == '/'
            || pattern.Contains('\\', StringComparison.Ordinal)
            || pattern.Split('/').Any(static segment => segment is "" or "." or ".."))
        {
            throw new FormatException($"unsafe engineering input pattern: {pattern}");
        }

        var expression = new StringBuilder("\\A");
        for (var index = 0; index < pattern.Length; index++)
        {
            if (pattern[index] == '*' && index + 1 < pattern.Length && pattern[index + 1] == '*')
            {
                if (index + 2 < pattern.Length && pattern[index + 2] == '/')
                {
                    expression.Append("(?:.*/)?");
                    index++;
                }
                else
                {
                    expression.Append(".*");
                }
                index++;
            }
            else
            {
                expression.Append(pattern[index] switch
                {
                    '*' => "[^/]*",
                    '?' => "[^/]",
                    _ => Regex.Escape(pattern[index].ToString()),
                });
            }
        }

        return new Regex(expression.Append("\\z").ToString(), RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    }
}
