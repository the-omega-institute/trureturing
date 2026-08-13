using StrataLint.Engine;
using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed class MakeTestExecutionClosureTests
{
    [Fact]
    public void RequiredCiJobsExecuteExactlyEveryIndexedXunitProject()
    {
        var root = FindRepositoryRoot();
        var indexedFiles = GitIndexRepositoryFiles.Enumerate(root);
        var projects = indexedFiles
            .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => new RepositoryBuildFile(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        var solutions = indexedFiles
            .Where(static file => file.RelativePath.EndsWith(".sln", StringComparison.Ordinal))
            .Select(file => new RepositoryBuildFile(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();

        var coverage = MakeTestExecutionClosure.Inspect(
            projects,
            solutions,
            File.ReadAllText(Path.Combine(root, "Makefile")),
            File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml")));

        Assert.True(coverage.IsComplete, coverage.FormatFailure());
        Assert.Equal(coverage.ExpectedProjects, coverage.ExecutedProjects);
        Assert.Empty(coverage.IncompleteInvocations);
    }

    [Fact]
    public void ClosureRejectsAnXunitProjectMissingFromTheExecutedSolutionAsARedFixture()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj")],
            Makefile("dotnet test Tests.sln --configuration Release"),
            Workflow("make -C candidate test-all"));

        Assert.False(coverage.IsComplete);
        Assert.Equal(["Three/Three.csproj"], coverage.MissingProjects);
        Assert.Empty(coverage.ExtraProjects);
    }

    [Fact]
    public void ClosureRejectsFilteredDotnetTestAsARedFixture()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj", "Three/Three.csproj")],
            Makefile("dotnet test Tests.sln --filter Category=Fast"),
            Workflow("make -C candidate test-all"));

        Assert.False(coverage.IsComplete);
        var invocation = Assert.Single(coverage.IncompleteInvocations);
        Assert.Contains("--filter", invocation, StringComparison.Ordinal);
    }

    [Fact]
    public void ClosureRejectsAFilterAttachedToAnyWorkflowMakeInvocationAsARedFixture()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj", "Three/Three.csproj")],
            Makefile("dotnet test Tests.sln"),
            Workflow("make -C candidate test-all --filter Category=Fast"));

        Assert.False(coverage.IsComplete);
        var invocation = Assert.Single(coverage.IncompleteInvocations);
        Assert.Contains("--filter", invocation, StringComparison.Ordinal);
    }

    [Fact]
    public void ClosureExpandsSolutionProjectsThroughChainedMakeTargets()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj", "Three/Three.csproj")],
            string.Join('\n',
                "test:",
                "\t@/bin/bash check.sh",
                "test-harness:",
                "\t@dotnet test Tests.sln --configuration Release",
                "test-all:",
                "\t@$(MAKE) --no-print-directory test",
                "\t@$(MAKE) --no-print-directory test-harness",
                string.Empty),
            Workflow("make -C candidate test-all"));

        Assert.True(coverage.IsComplete, coverage.FormatFailure());
        Assert.Equal(coverage.ExpectedProjects, coverage.ExecutedProjects);
    }

    [Fact]
    public void LexicalGuardRejectsConditionalOrShortCircuitRecipeAsAWordBoundaryRedFixture()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj", "Three/Three.csproj")],
            string.Join('\n',
                "test:",
                "\t@dotnet test Tests.sln --configuration Release",
                "test-harness:",
                "\t@dotnet test Tests.sln --configuration Release",
                "test-all:",
                "\t@if [ -n \"$$SKIP_HARNESS\" ]; then $(MAKE) --no-print-directory test; else $(MAKE) --no-print-directory test && $(MAKE) --no-print-directory test-harness; fi",
                string.Empty),
            Workflow("make -C candidate test-all"));

        Assert.False(coverage.IsComplete);
        var finding = Assert.Single(coverage.IncompleteInvocations);
        Assert.Contains("conditional/short-circuit shell control flow", finding, StringComparison.Ordinal);
    }

    [Fact]
    public void ClosureRejectsConditionalRecipeThatOmitsAProjectAsAClosureViolationRedFixture()
    {
        var coverage = MakeTestExecutionClosure.Inspect(
            ThreeXunitProjects(),
            [Solution("Tests.sln", "One/One.csproj", "Two/Two.csproj", "Three/Three.csproj")],
            string.Join('\n',
                "test:",
                "\t@dotnet test Tests.sln --configuration Release",
                "test-harness:",
                "\t@dotnet test Tests.sln --configuration Release",
                "test-all:",
                "\t@if [ -n \"$$FAST\" ]; then dotnet test One/One.csproj; fi",
                string.Empty),
            Workflow("make -C candidate test-all"));

        Assert.False(coverage.IsComplete);
        Assert.Equal(["Three/Three.csproj", "Two/Two.csproj"], coverage.MissingProjects);
        var finding = Assert.Single(coverage.IncompleteInvocations);
        Assert.Contains("project closure cannot prove the conditional target covers the full test set", finding, StringComparison.Ordinal);
        Assert.DoesNotContain("conditional/short-circuit shell control flow", finding, StringComparison.Ordinal);
    }

    private static RepositoryBuildFile[] ThreeXunitProjects() =>
    [
        XunitProject("One/One.csproj"),
        XunitProject("Two/Two.csproj"),
        XunitProject("Three/Three.csproj"),
    ];

    private static RepositoryBuildFile XunitProject(string path) => new(
        path,
        "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>");

    private static RepositoryBuildFile Solution(string path, params string[] projects) => new(
        path,
        string.Join('\n', projects.Select((project, index) =>
            $"Project(\"{{TYPE-{index}}}\") = \"Project{index}\", \"{project}\", \"{{PROJECT-{index}}}\"")));

    private static string Makefile(string dotnetTest) => string.Join('\n',
        "test-harness:",
        $"\t@{dotnetTest}",
        "test-all:",
        "\t@$(MAKE) --no-print-directory test-harness",
        string.Empty);

    private static string Workflow(string run) =>
        $"""
        jobs:
          required:
            steps:
              - name: Execute tests
                run: {run}
        """;

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}

internal sealed record RepositoryBuildFile(string Path, string Content);

internal sealed record MakeTestCoverage(
    IReadOnlyList<string> ExpectedProjects,
    IReadOnlyList<string> ExecutedProjects,
    IReadOnlyList<string> MissingProjects,
    IReadOnlyList<string> ExtraProjects,
    IReadOnlyList<string> IncompleteInvocations)
{
    internal bool IsComplete =>
        MissingProjects.Count == 0
        && ExtraProjects.Count == 0
        && IncompleteInvocations.Count == 0;

    internal string FormatFailure() =>
        $"Expected xUnit projects: {string.Join(", ", ExpectedProjects)}\n"
        + $"Executed xUnit projects: {string.Join(", ", ExecutedProjects)}\n"
        + $"Missing: {string.Join(", ", MissingProjects)}\n"
        + $"Extra or dangling: {string.Join(", ", ExtraProjects)}\n"
        + $"Incomplete invocations: {string.Join(" | ", IncompleteInvocations)}\n"
        + "This guard proves project-level closure only; it does not prove xUnit collected every Fact within a covered project."
        + " Workflow if: conditions and shell control flow are not modeled; conditional or short-circuit recipes are rejected instead of being treated as complete.";
}

internal static class MakeTestExecutionClosure
{
    private static readonly Regex MakeInvocation = new(
        @"(?m)^[ \t]*(?:[A-Za-z_][A-Za-z0-9_]*=[^ \t]+[ \t]+)*make[ \t]+-C[ \t]+candidate[ \t]+(?<target>[A-Za-z][A-Za-z0-9_-]*)(?<arguments>[^\r\n]*)$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex NestedMakeInvocation = new(
        @"(?:\$\(MAKE\)|make)[ \t]+(?:--no-print-directory[ \t]+)*(?<target>[A-Za-z][A-Za-z0-9_-]*)",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex DotnetTestInvocation = new(
        @"dotnet[ \t]+test(?<arguments>[^\r\n;&|]*)",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex ConditionalShellControlFlow = new(
        @"&&|\|\||(?m)^\s*@?(?:if|then|else|elif|fi)\b",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex CommandToken = new(
        "\"[^\"]*\"|'[^']*'|[^ \\t]+",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex SolutionProject = new(
        "(?m)^Project\\([^\\r\\n]*\\)[ \\t]*=[ \\t]*\"[^\"]*\",[ \\t]*\"(?<path>[^\"]+\\.csproj)\",",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    internal static MakeTestCoverage Inspect(
        IReadOnlyList<RepositoryBuildFile> projects,
        IReadOnlyList<RepositoryBuildFile> solutions,
        string makefile,
        string workflow)
    {
        var projectsByPath = projects.ToDictionary(
            static project => NormalizePath(project.Path),
            StringComparer.Ordinal);
        var solutionsByPath = solutions.ToDictionary(
            static solution => NormalizePath(solution.Path),
            StringComparer.Ordinal);
        var expected = projectsByPath.Values
            .Where(static project => ProjectFileClassifier.IsXunitProject(project.Content))
            .Select(static project => NormalizePath(project.Path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        var executed = new HashSet<string>(StringComparer.Ordinal);
        var incomplete = new List<string>();
        var targets = ParseTargets(makefile);

        foreach (var invocation in RequiredMakeInvocations(workflow))
        {
            if (invocation.Arguments.Contains("--filter", StringComparison.Ordinal))
            {
                incomplete.Add(invocation.Command.Trim());
                continue;
            }

            InspectTarget(
                invocation.Target,
                targets,
                projectsByPath,
                solutionsByPath,
                executed,
                incomplete,
                new HashSet<string>(StringComparer.Ordinal));
        }

        var executedProjects = executed.Order(StringComparer.Ordinal).ToArray();
        return new MakeTestCoverage(
            expected,
            executedProjects,
            expected.Except(executedProjects, StringComparer.Ordinal).ToArray(),
            executedProjects.Except(expected, StringComparer.Ordinal).ToArray(),
            incomplete);
    }

    private static IReadOnlyList<WorkflowMakeInvocation> RequiredMakeInvocations(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = (YamlMappingNode)stream.Documents[0].RootNode;
        var jobs = (YamlMappingNode)document.Children[new YamlScalarNode("jobs")];
        return jobs.Children.Values
            .OfType<YamlMappingNode>()
            .Where(static job => job.Children.ContainsKey(new YamlScalarNode("steps")))
            .SelectMany(static job => ((YamlSequenceNode)job.Children[new YamlScalarNode("steps")]).Children)
            .OfType<YamlMappingNode>()
            .Where(static step => step.Children.ContainsKey(new YamlScalarNode("run")))
            .Select(static step => ((YamlScalarNode)step.Children[new YamlScalarNode("run")]).Value ?? string.Empty)
            .SelectMany(run => MakeInvocation.Matches(run).Select(static match => new WorkflowMakeInvocation(
                match.Groups["target"].Value,
                match.Groups["arguments"].Value,
                match.Value)))
            .ToArray();
    }

    private static void InspectTarget(
        string target,
        IReadOnlyDictionary<string, MakeTarget> targets,
        IReadOnlyDictionary<string, RepositoryBuildFile> projects,
        IReadOnlyDictionary<string, RepositoryBuildFile> solutions,
        ISet<string> executed,
        ICollection<string> incomplete,
        ISet<string> visited)
    {
        if (!visited.Add(target))
        {
            return;
        }

        if (!targets.TryGetValue(target, out var makeTarget))
        {
            incomplete.Add($"make target is absent: {target}");
            return;
        }

        if (ConditionalShellControlFlow.IsMatch(makeTarget.Recipe))
        {
            if (makeTarget.Recipe.Contains(".csproj", StringComparison.Ordinal)
                && !makeTarget.Recipe.Contains(".sln", StringComparison.Ordinal))
            {
                foreach (Match invocation in DotnetTestInvocation.Matches(makeTarget.Recipe))
                    InspectDotnetTest(invocation.Value, projects, solutions, executed, incomplete);
                incomplete.Add(
                    $"project closure cannot prove the conditional target covers the full test set: {makeTarget.Recipe.Trim()}");
                return;
            }
            incomplete.Add(
                $"make target '{target}' uses conditional/short-circuit shell control flow; project closure cannot prove both branches execute");
            return;
        }

        foreach (var dependency in makeTarget.Dependencies)
        {
            InspectTarget(dependency, targets, projects, solutions, executed, incomplete, visited);
        }

        foreach (Match nested in NestedMakeInvocation.Matches(makeTarget.Recipe))
        {
            InspectTarget(
                nested.Groups["target"].Value,
                targets,
                projects,
                solutions,
                executed,
                incomplete,
                visited);
        }

        foreach (Match invocation in DotnetTestInvocation.Matches(makeTarget.Recipe))
        {
            InspectDotnetTest(invocation.Value, projects, solutions, executed, incomplete);
        }
    }

    private static void InspectDotnetTest(
        string invocation,
        IReadOnlyDictionary<string, RepositoryBuildFile> projects,
        IReadOnlyDictionary<string, RepositoryBuildFile> solutions,
        ISet<string> executed,
        ICollection<string> incomplete)
    {
        var tokens = CommandToken.Matches(invocation)
            .Select(static match => match.Value.Trim('"', '\''))
            .ToArray();
        if (tokens.Any(static token => token == "--filter" || token.StartsWith("--filter=", StringComparison.Ordinal)))
        {
            incomplete.Add(invocation.Trim());
            return;
        }

        var input = tokens.FirstOrDefault(static token =>
            token.EndsWith(".sln", StringComparison.OrdinalIgnoreCase)
            || token.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase));
        if (input is null)
        {
            if (invocation.Contains('$', StringComparison.Ordinal))
            {
                incomplete.Add(
                    $"project closure cannot prove the conditional target covers the full test set: {invocation.Trim()}");
                return;
            }
            incomplete.Add($"dotnet test has no explicit solution or project: {invocation.Trim()}");
            return;
        }

        var normalizedInput = NormalizePath(input);
        if (normalizedInput.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase))
        {
            executed.Add(normalizedInput);
            return;
        }

        if (!solutions.TryGetValue(normalizedInput, out var solution))
        {
            executed.Add(normalizedInput);
            return;
        }

        var solutionDirectory = normalizedInput.Contains('/', StringComparison.Ordinal)
            ? normalizedInput[..normalizedInput.LastIndexOf('/')]
            : string.Empty;
        foreach (Match project in SolutionProject.Matches(solution.Content))
        {
            var path = NormalizePath(
                string.IsNullOrEmpty(solutionDirectory)
                    ? project.Groups["path"].Value
                    : solutionDirectory + "/" + project.Groups["path"].Value);
            if (!projects.TryGetValue(path, out var manifest)
                || ProjectFileClassifier.IsXunitProject(manifest.Content))
            {
                executed.Add(path);
            }
        }
    }

    private static IReadOnlyDictionary<string, MakeTarget> ParseTargets(string makefile)
    {
        var targets = new Dictionary<string, MakeTarget>(StringComparer.Ordinal);
        var lines = makefile.Split('\n');
        for (var index = 0; index < lines.Length; index++)
        {
            var separator = lines[index].IndexOf(':');
            if (separator <= 0 || lines[index][0] is ' ' or '\t' || lines[index].Contains(" := ", StringComparison.Ordinal))
            {
                continue;
            }

            var name = lines[index][..separator];
            if (!Regex.IsMatch(name, @"^[A-Za-z][A-Za-z0-9_-]*$", RegexOptions.CultureInvariant))
            {
                continue;
            }

            var dependencies = lines[index][(separator + 1)..]
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)
                .Where(static dependency => Regex.IsMatch(
                    dependency,
                    @"^[A-Za-z][A-Za-z0-9_-]*$",
                    RegexOptions.CultureInvariant))
                .ToArray();
            var recipe = lines
                .Skip(index + 1)
                .TakeWhile(static line => line.Length == 0 || line[0] == '\t')
                .Where(static line => line.StartsWith('\t'));
            targets[name] = new MakeTarget(dependencies, string.Join('\n', recipe));
        }

        return targets;
    }

    private static string NormalizePath(string path)
    {
        var normalized = new List<string>();
        foreach (var segment in path.Replace('\\', '/').Split('/', StringSplitOptions.RemoveEmptyEntries))
        {
            if (segment == ".")
            {
                continue;
            }
            if (segment == "..")
            {
                if (normalized.Count > 0)
                {
                    normalized.RemoveAt(normalized.Count - 1);
                }
                continue;
            }
            normalized.Add(segment);
        }
        return string.Join('/', normalized);
    }

    private sealed record MakeTarget(IReadOnlyList<string> Dependencies, string Recipe);
    private sealed record WorkflowMakeInvocation(string Target, string Arguments, string Command);
}
