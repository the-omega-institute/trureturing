using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record EngineeringProjectInput(string Path, string Content);

internal sealed record EngineeringInputClosure(
    ImmutableArray<string> PathRoots,
    ImmutableArray<string> ProjectInputPatterns,
    bool IsComplete,
    string? IncompleteReason);

internal enum EngineeringScopeReason
{
    ConsumerDerivedInput,
    ProvenDisjoint,
    IncompleteDerivation,
}

internal sealed record EngineeringScopeDecision(
    bool Run,
    ImmutableArray<string> MatchedPaths,
    EngineeringScopeReason Reason,
    string Detail);

internal static class EngineeringInputDeriver
{
    private static readonly ImmutableHashSet<string> RepositoryInputItemTypes =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "AdditionalFiles",
            "Compile",
            "Content",
            "EmbeddedResource",
            "None",
            "ProjectReference");

    internal static EngineeringInputClosure DeriveRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var projects = files
            .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => new EngineeringProjectInput(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        var repositoryReads = map.Methods
            .SelectMany(static method => method.Paths)
            .Concat(files
                .Select(static file => file.RelativePath)
                .Where(static path => !path.Contains('/', StringComparison.Ordinal)))
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        var structuralFailures = map.UnclassifiedManagedProjectPaths
            .Concat(map.OrphanManagedSourcePaths)
            .Concat(map.DanglingCompileFailProofProjectExemptionPaths)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var unknownConsumerCount = map.Methods.Count(static method => method.IsUnknown);
        var incompleteReasons = new List<string>();
        if (structuralFailures.Length != 0)
        {
            incompleteReasons.Add("test project classification is incomplete: "
                + string.Join(", ", structuralFailures));
        }
        if (unknownConsumerCount != 0)
        {
            incompleteReasons.Add($"{unknownConsumerCount} test consumers have inputs that are not statically closed");
        }

        return DeriveProjectInputs(
            repositoryRoot,
            projects,
            repositoryReads,
            incompleteReasons.Count == 0,
            incompleteReasons.Count == 0 ? null : string.Join("; ", incompleteReasons));
    }

    internal static EngineeringInputClosure DeriveProjectInputs(
        string repositoryRoot,
        IReadOnlyList<EngineeringProjectInput> projects,
        IReadOnlyList<string> repositoryReads,
        bool isComplete = true,
        string? incompleteReason = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(projects);
        ArgumentNullException.ThrowIfNull(repositoryReads);

        var roots = repositoryReads
            .Select(NormalizeRepositoryPath)
            .ToHashSet(StringComparer.Ordinal);
        var patterns = new HashSet<string>(StringComparer.Ordinal);
        var failures = new List<string>();
        if (!isComplete && !string.IsNullOrWhiteSpace(incompleteReason))
        {
            failures.Add(incompleteReason);
        }

        var projectPaths = projects
            .Select(static project => project.Path)
            .Select(NormalizeRepositoryPath)
            .ToArray();
        var projectRoot = CommonDirectory(projectPaths);
        if (projectRoot is null)
        {
            failures.Add("no common project root can be derived");
        }
        else
        {
            roots.Add(projectRoot);
        }

        foreach (var project in projects)
        {
            try
            {
                var document = XDocument.Parse(project.Content, LoadOptions.None);
                foreach (var item in document.Descendants()
                    .Where(element => RepositoryInputItemTypes.Contains(element.Name.LocalName)))
                {
                    var include = (string?)item.Attribute("Include");
                    if (string.IsNullOrWhiteSpace(include))
                    {
                        continue;
                    }

                    foreach (var value in include.Split(';', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
                    {
                        if (value.Contains("$(", StringComparison.Ordinal))
                        {
                            failures.Add($"{project.Path} has an unevaluated repository input: {value}");
                            continue;
                        }

                        var resolved = ResolveProjectInput(project.Path, value);
                        if (resolved is null)
                        {
                            failures.Add($"{project.Path} has an input outside the repository: {value}");
                            continue;
                        }

                        if (projectRoot is not null && Covers(projectRoot, resolved))
                        {
                            continue;
                        }

                        try
                        {
                            EngineeringInputGlob.Validate(resolved);
                            patterns.Add(resolved);
                        }
                        catch (FormatException exception)
                        {
                            failures.Add($"{project.Path} has an invalid repository input {value}: {exception.Message}");
                        }
                    }
                }
            }
            catch (Exception exception) when (exception is System.Xml.XmlException or InvalidOperationException)
            {
                failures.Add($"cannot parse {project.Path}: {exception.Message}");
            }
        }

        return new EngineeringInputClosure(
            [.. roots.Order(StringComparer.Ordinal)],
            [.. patterns.Order(StringComparer.Ordinal)],
            failures.Count == 0,
            failures.Count == 0 ? null : string.Join("; ", failures));
    }

    private static string? CommonDirectory(IReadOnlyList<string> paths)
    {
        if (paths.Count == 0)
        {
            return null;
        }

        var common = paths[0].Split('/').SkipLast(1).ToArray();
        foreach (var path in paths.Skip(1))
        {
            var segments = path.Split('/');
            var length = Math.Min(common.Length, segments.Length - 1);
            var index = 0;
            while (index < length && string.Equals(common[index], segments[index], StringComparison.Ordinal))
            {
                index++;
            }

            common = common[..index];
        }

        return common.Length == 0 ? null : string.Join('/', common);
    }

    private static string? ResolveProjectInput(string projectPath, string include)
    {
        var segments = new List<string>();
        var projectDirectory = projectPath.Split('/').SkipLast(1);
        foreach (var segment in projectDirectory.Concat(include.Replace('\\', '/').Split('/')))
        {
            switch (segment)
            {
                case "" or ".":
                    continue;
                case ".." when segments.Count == 0:
                    return null;
                case "..":
                    segments.RemoveAt(segments.Count - 1);
                    break;
                default:
                    segments.Add(segment);
                    break;
            }
        }

        return segments.Count == 0 ? null : string.Join('/', segments);
    }

    private static string NormalizeRepositoryPath(string path)
    {
        if (string.IsNullOrWhiteSpace(path)
            || !string.Equals(path, path.Trim(), StringComparison.Ordinal)
            || path[0] == '/'
            || path.Contains('\\', StringComparison.Ordinal)
            || path.Contains("//", StringComparison.Ordinal)
            || path.Split('/').Any(static segment => segment is "" or "." or ".."))
        {
            throw new FormatException($"invalid repository input path: {path}");
        }

        return path;
    }

    private static bool Covers(string root, string path) =>
        path == root || path.StartsWith(root + "/", StringComparison.Ordinal);
}

internal static class EngineeringScopePolicy
{
    internal static EngineeringScopeDecision Evaluate(
        IReadOnlyList<string> changedPaths,
        EngineeringInputClosure closure)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        ArgumentNullException.ThrowIfNull(closure);
        var matched = changedPaths
            .Where(path => MatchesDerivedInput(path, closure))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (!closure.IsComplete)
        {
            return new EngineeringScopeDecision(
                true,
                matched,
                EngineeringScopeReason.IncompleteDerivation,
                closure.IncompleteReason ?? "engineering input derivation is incomplete");
        }

        return matched.Length == 0
            ? new EngineeringScopeDecision(
                false,
                [],
                EngineeringScopeReason.ProvenDisjoint,
                "candidate delta is disjoint from the consumer-derived engineering input closure")
            : new EngineeringScopeDecision(
                true,
                matched,
                EngineeringScopeReason.ConsumerDerivedInput,
                "candidate delta intersects the consumer-derived engineering input closure");
    }

    private static bool MatchesDerivedInput(string path, EngineeringInputClosure closure) =>
        closure.PathRoots.Any(root => Covers(root, path))
        || closure.ProjectInputPatterns.Any(pattern => EngineeringInputGlob.IsMatch(pattern, path));

    private static bool Covers(string root, string path) =>
        path == root || path.StartsWith(root + "/", StringComparison.Ordinal);
}

internal static class EngineeringInputGlob
{
    internal static void Validate(string pattern) => _ = CreateRegex(pattern);

    internal static bool IsMatch(string pattern, string path) => CreateRegex(pattern).IsMatch(path);

    private static Regex CreateRegex(string pattern)
    {
        if (string.IsNullOrWhiteSpace(pattern)
            || !string.Equals(pattern, pattern.Trim(), StringComparison.Ordinal)
            || pattern[0] == '/'
            || pattern.Contains('\\', StringComparison.Ordinal)
            || pattern.Contains("//", StringComparison.Ordinal)
            || pattern.Any(static character => character is < ' ' or > '~')
            || pattern.Split('/').Any(static segment => segment is "" or "." or ".."))
        {
            throw new FormatException($"unsafe engineering input pattern: {pattern}");
        }

        var expression = new StringBuilder("\\A");
        for (var index = 0; index < pattern.Length; index++)
        {
            var character = pattern[index];
            if (character == '*' && index + 1 < pattern.Length && pattern[index + 1] == '*')
            {
                if (index + 2 < pattern.Length && pattern[index + 2] == '/')
                {
                    expression.Append("(?:.*/)?");
                    index += 2;
                }
                else
                {
                    expression.Append(".*");
                    index++;
                }

                continue;
            }

            expression.Append(character switch
            {
                '*' => "[^/]*",
                '?' => "[^/]",
                _ => Regex.Escape(character.ToString()),
            });
        }

        expression.Append("\\z");
        return new Regex(
            expression.ToString(),
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    }
}
