using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum EngineeringTestPlanKind { Full, Selected, None }

internal enum EngineeringSelectedTestReason { UnknownInput, DeclaredInput, CompiledInput }

internal sealed record EngineeringSelectedTest(
    string ProjectPath,
    string Id,
    EngineeringSelectedTestReason Reason,
    string Detail);

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
}

internal static class EngineeringTestPlanPolicy
{
    internal static EngineeringTestPlan Evaluate(
        IReadOnlyList<string> changedPaths,
        ScribeTestMap map,
        IReadOnlySet<string> compileAffectedTestProjects,
        string? attributionFailure = null)
    {
        var changed = changedPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
        if (changed.Any(IsFullSurface))
        {
            return Full(changed, "candidate delta changes the engineering implementation or a repository-root build input");
        }

        var failures = map.UnclassifiedManagedProjectPaths
            .Concat(map.OrphanManagedSourcePaths)
            .Concat(map.DanglingCompileFailProofProjectExemptionPaths)
            .Concat(map.CompileQueryFindings.Select(static finding => finding.Path))
            .ToArray();
        if (attributionFailure is not null || failures.Length != 0)
        {
            var detail = attributionFailure ?? string.Join(", ", failures.Order(StringComparer.Ordinal));
            return Full(changed, $"project attribution failed: {detail}");
        }

        var tests = new List<EngineeringSelectedTest>();
        foreach (var method in map.Methods)
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
                    detail = "target has repository inputs that are not statically closed";
                }
            }

            if (reason is not null)
            {
                tests.Add(new EngineeringSelectedTest(project, method.Id, reason.Value, detail!));
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
                $"selected {selected.Length} affected or locally conservative test targets");
    }

    internal static EngineeringTestPlan Full(IReadOnlyList<string> changedPaths, string reason) => new(
        EngineeringTestPlanKind.Full,
        changedPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
        [],
        reason);

    private static bool IsFullSurface(string path) =>
        path == "tools" || path.StartsWith("tools/", StringComparison.Ordinal) || !path.Contains('/');

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
            return run(new EngineeringTestInvocation("tools/StrataLint.sln", null, []));

        var filter = string.Join('|', plan.Tests.Select(static test => $"FullyQualifiedName~{test.Id}").Distinct(StringComparer.Ordinal));
        try
        {
            if (run(new EngineeringTestInvocation("tools/StrataLint.sln", filter, plan.Tests)) == 0) return 0;
        }
        catch (Exception) { }
        return run(new EngineeringTestInvocation("tools/StrataLint.sln", null, []));
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
            var projects = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
                .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
                .Select(file => ParseProject(file.RelativePath, File.ReadAllText(file.FullPath)))
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
