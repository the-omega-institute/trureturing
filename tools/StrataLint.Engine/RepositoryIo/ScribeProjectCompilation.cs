using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ScribeCompilationProject(
    string Path,
    string ProjectContent,
    string AssemblyName,
    IReadOnlyList<string> ProjectReferences,
    IReadOnlyList<ScribeTrackedSource> Sources,
    string? PackageLockContent);

internal sealed record ScribeProjectCompilation(
    string ProjectPath,
    CSharpCompilation Compilation,
    IReadOnlyList<(TestMapSource Source, SyntaxTree Tree)> GovernedSources,
    ScribeMetadataDegradation? MetadataDegradation);

internal sealed record ScribeProjectCompilationContext(
    IReadOnlyList<ScribeCompilationProject> Projects,
    IReadOnlySet<string> ProductionAssemblies)
{
    internal static ScribeProjectCompilationContext Create(
        IReadOnlyList<ScribeTrackedSource> files,
        IReadOnlyDictionary<string, string> projectBySourcePath,
        IReadOnlySet<string> testProjectPaths)
    {
        var projectFiles = files
            .Where(static file => file.Path.EndsWith(".csproj", StringComparison.Ordinal))
            .ToDictionary(static file => file.Path, StringComparer.Ordinal);
        var sourcesByProject = files
            .Where(static file => file.Path.EndsWith(".cs", StringComparison.Ordinal))
            .Where(file => projectBySourcePath.ContainsKey(file.Path))
            .GroupBy(file => projectBySourcePath[file.Path], StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => (IReadOnlyList<ScribeTrackedSource>)group
                    .OrderBy(static source => source.Path, StringComparer.Ordinal)
                    .ToArray(),
                StringComparer.Ordinal);
        var contentByPath = files.ToDictionary(static file => file.Path, StringComparer.Ordinal);
        var projects = projectFiles.Values
            .Select(file => ParseProject(
                file,
                sourcesByProject.GetValueOrDefault(file.Path) ?? [],
                contentByPath.GetValueOrDefault(Combine(ProjectDirectory(file.Path), "packages.lock.json"))?.Content))
            .OrderBy(static project => project.Path, StringComparer.Ordinal)
            .ToArray();
        var productionAssemblies = projects
            .Where(project => !testProjectPaths.Contains(project.Path))
            .Select(static project => project.AssemblyName)
            .ToHashSet(StringComparer.Ordinal);
        return new ScribeProjectCompilationContext(projects, productionAssemblies);
    }

    internal static bool IsXunitProject(string content)
    {
        var document = XDocument.Parse(content, LoadOptions.None);
        return document.Descendants().Any(static element =>
            element.Name.LocalName == "PackageReference"
            && string.Equals(
                (string?)element.Attribute("Include"),
                "xunit",
                StringComparison.OrdinalIgnoreCase));
    }

    private static ScribeCompilationProject ParseProject(
        ScribeTrackedSource project,
        IReadOnlyList<ScribeTrackedSource> sources,
        string? packageLockContent)
    {
        var document = XDocument.Parse(project.Content, LoadOptions.None);
        var assemblyName = document.Descendants()
            .FirstOrDefault(static element => element.Name.LocalName == "AssemblyName")?.Value.Trim();
        if (string.IsNullOrEmpty(assemblyName))
        {
            assemblyName = Path.GetFileNameWithoutExtension(project.Path);
        }

        var references = document.Descendants()
            .Where(static element => element.Name.LocalName == "ProjectReference")
            .Select(static element => (string?)element.Attribute("Include"))
            .Where(static include => !string.IsNullOrWhiteSpace(include))
            .Select(include => Combine(ProjectDirectory(project.Path), include!))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        return new ScribeCompilationProject(
            project.Path,
            project.Content,
            assemblyName,
            references,
            sources,
            packageLockContent);
    }

    private static string ProjectDirectory(string path) =>
        path.LastIndexOf('/') is var slash && slash >= 0 ? path[..slash] : ".";

    private static string Combine(string directory, string relative)
    {
        var segments = new List<string>();
        foreach (var segment in (directory + "/" + relative.Replace('\\', '/'))
                     .Split('/', StringSplitOptions.RemoveEmptyEntries))
        {
            if (segment == ".") continue;
            if (segment == "..")
            {
                if (segments.Count != 0) segments.RemoveAt(segments.Count - 1);
                continue;
            }
            segments.Add(segment);
        }
        return string.Join('/', segments);
    }
}

internal static class ScribeProjectCompilationBuilder
{
    private static readonly CSharpParseOptions ParseOptions = CSharpParseOptions.Default
        .WithLanguageVersion(LanguageVersion.Preview)
        .WithPreprocessorSymbols("NET", "NET10_0", "NET10_0_OR_GREATER");

    internal static IReadOnlyList<ScribeProjectCompilation> Build(
        IReadOnlyList<TestMapSource> governedSources,
        ScribeProjectCompilationContext? context,
        IReadOnlyList<MetadataReference>? syntheticXunitMetadataReferences = null)
    {
        if (context is null)
        {
            return BuildSynthetic(governedSources, syntheticXunitMetadataReferences);
        }
        if (syntheticXunitMetadataReferences is not null)
        {
            throw new ArgumentException(
                "synthetic xUnit metadata references cannot be combined with a project compilation context",
                nameof(syntheticXunitMetadataReferences));
        }

        var governedByPath = governedSources.ToDictionary(static source => source.Path, StringComparer.Ordinal);
        var projectsByPath = context.Projects.ToDictionary(static project => project.Path, StringComparer.Ordinal);
        var compilations = new Dictionary<string, CSharpCompilation>(StringComparer.Ordinal);
        var degradations = new Dictionary<string, ScribeMetadataDegradation?>(StringComparer.Ordinal);
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        CSharpCompilation BuildProject(string path)
        {
            if (compilations.TryGetValue(path, out var existing)) return existing;
            var project = projectsByPath[path];
            if (!visiting.Add(path))
            {
                throw new InvalidOperationException($"project reference cycle reaches {path}");
            }

            foreach (var referencePath in project.ProjectReferences)
            {
                if (!projectsByPath.ContainsKey(referencePath))
                {
                    throw new InvalidOperationException(
                        $"{path} references absent project {referencePath}");
                }
                BuildProject(referencePath);
            }
            var projectReferences = TransitiveProjectReferences(project, projectsByPath)
                .Select(reference => compilations[reference.Path].ToMetadataReference());
            var trees = project.Sources
                .Select(source => CSharpSyntaxTree.ParseText(source.Content, ParseOptions, source.Path))
                .Append(ImplicitUsingsTree(project.Path))
                .ToList();
            var resolution = ScribeMetadataReferenceResolver.Resolve(project);
            if (resolution.Degradation?.NeedsXunitAttributeFallback == true)
            {
                trees.Add(XunitAttributeFallbackTree(project.Path));
            }
            var references = resolution.References
                .Concat(projectReferences)
                .ToArray();
            var compilation = CSharpCompilation.Create(
                project.AssemblyName,
                trees,
                references,
                CompilationOptions());
            visiting.Remove(path);
            compilations.Add(path, compilation);
            degradations.Add(path, resolution.Degradation);
            return compilation;
        }

        foreach (var project in context.Projects) BuildProject(project.Path);
        return context.Projects.Select(project =>
        {
            var compilation = compilations[project.Path];
            var sources = compilation.SyntaxTrees
                .Where(tree => governedByPath.ContainsKey(tree.FilePath))
                .Select(tree => (governedByPath[tree.FilePath], tree))
                .ToArray();
            return new ScribeProjectCompilation(
                project.Path,
                compilation,
                sources,
                degradations[project.Path]);
        }).ToArray();
    }

    private static IReadOnlyList<ScribeProjectCompilation> BuildSynthetic(
        IReadOnlyList<TestMapSource> sources,
        IReadOnlyList<MetadataReference>? xunitMetadataReferences) => sources
        .GroupBy(static source => source.PartitionKey, StringComparer.Ordinal)
        .OrderBy(static group => group.Key, StringComparer.Ordinal)
        .Select(group =>
        {
            var parsed = group.Select(source => (
                Source: source,
                Tree: CSharpSyntaxTree.ParseText(source.Content, ParseOptions, source.Path))).ToArray();
            var support = SyntheticSupportTree(
                parsed.Select(static item => item.Tree.GetRoot()),
                includeXunitFallback: xunitMetadataReferences is null);
            var compilation = CSharpCompilation.Create(
                AssemblyName(group.Key),
                parsed.Select(static item => item.Tree).Append(support),
                ScribeMetadataReferenceResolver.PlatformReferences()
                    .Concat(xunitMetadataReferences ?? []),
                CompilationOptions());
            return new ScribeProjectCompilation(
                group.Key,
                compilation,
                parsed.Select(static item => (item.Source, (SyntaxTree)item.Tree)).ToArray(),
                null);
        }).ToArray();

    private static IEnumerable<ScribeCompilationProject> TransitiveProjectReferences(
        ScribeCompilationProject project,
        IReadOnlyDictionary<string, ScribeCompilationProject> projectsByPath)
    {
        var pending = new Stack<string>(project.ProjectReferences.Reverse());
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryPop(out var path))
        {
            if (!visited.Add(path) || !projectsByPath.TryGetValue(path, out var target)) continue;
            yield return target;
            foreach (var reference in target.ProjectReferences.Reverse()) pending.Push(reference);
        }
    }

    private static CSharpCompilationOptions CompilationOptions() => new(
        OutputKind.DynamicallyLinkedLibrary,
        allowUnsafe: true,
        nullableContextOptions: NullableContextOptions.Enable);

    private static SyntaxTree ImplicitUsingsTree(string projectPath) => CSharpSyntaxTree.ParseText(
        """
        global using System;
        global using System.Collections.Generic;
        global using System.IO;
        global using System.Linq;
        global using System.Net.Http;
        global using System.Threading;
        global using System.Threading.Tasks;
        """,
        ParseOptions,
        projectPath + ".ImplicitUsings.g.cs");

    private static SyntaxTree XunitAttributeFallbackTree(string projectPath) =>
        CSharpSyntaxTree.ParseText(
            ("namespace " + "Xunit" + " {\n"
            + "  public class FactAttribute : System.Attribute { public virtual string? Skip { get; set; } }\n"
            + "  public class TheoryAttribute : FactAttribute { }\n"
            + "  public interface IClassFixture<TFixture> { }\n"
            + "}\n"),
            ParseOptions,
            projectPath + ".XunitMetadataFallback.g.cs");

    private static string SyntheticRepositorySupport(IReadOnlySet<string> declaredTypes) =>
        (declaredTypes.Contains("TemporaryFileSystem") ? string.Empty : """
            internal static class TemporaryFileSystem
            {
              internal static class File
              {
                internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);
                internal static string ReadAllText(string path) => System.IO.File.ReadAllText(path);
              }
              internal static class Directory
              {
                internal static System.IO.DirectoryInfo CreateTempSubdirectory(string? prefix = null) =>
                  System.IO.Directory.CreateTempSubdirectory(prefix);
              }
            }
            """)
        + (declaredTypes.Contains("RepositoryRoot") ? string.Empty : """
            internal readonly record struct RepositoryRoot(string FullPath);
            """)
        + (declaredTypes.Contains("RepositoryRelativePath") ? string.Empty : """
            internal readonly record struct RepositoryRelativePath(string Value)
            {
              internal static RepositoryRelativePath Create(string value) => new(value);
            }
            """)
        + (declaredTypes.Contains("RepositoryAccessor") ? string.Empty : """
            internal sealed class RepositoryAccessor
            {
              internal static RepositoryRoot Root { get; } = new(string.Empty);
              internal static RepositoryAccessor Discover(object criterion) => new();
              internal static string ReadAllText(RepositoryRelativePath path) => string.Empty;
            }
            """);

    private static SyntaxTree SyntheticSupportTree(
        IEnumerable<SyntaxNode> roots,
        bool includeXunitFallback)
    {
        var declaredTypes = roots.SelectMany(static root => root.DescendantNodes()
                .OfType<Microsoft.CodeAnalysis.CSharp.Syntax.TypeDeclarationSyntax>())
            .Select(static type => type.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var repositoryLayout = declaredTypes.Contains("RepositoryLayout")
            ? string.Empty
            : "internal static class RepositoryLayout { internal static string FindRoot() => string.Empty; }";
        var repositorySupport = SyntheticRepositorySupport(declaredTypes);
        return CSharpSyntaxTree.ParseText(
            ("global using System;\n"
            + "global using System.Collections.Generic;\n"
            + "global using System.IO;\n"
            + "global using System.Linq;\n"
            + "global using System.Net.Http;\n"
            + "global using System.Threading;\n"
            + "global using System.Threading.Tasks;\n"
            + "global using Xunit;\n"
            + (includeXunitFallback
                ? "namespace " + "Xunit {\n"
                    + "  public class FactAttribute : Attribute { public virtual string? Skip { get; set; } }\n"
                    + "  public class TheoryAttribute : FactAttribute { }\n"
                    + "  public interface IClassFixture<TFixture> { }\n"
                    + "}\n"
                : string.Empty)
            + repositoryLayout + "\n"
            + repositorySupport),
            ParseOptions,
            "ScribeSymbolSupport.g.cs");
    }

    private static string AssemblyName(string partitionKey) => partitionKey
        .Replace('\\', '/')
        .Split('/', StringSplitOptions.RemoveEmptyEntries)
        .LastOrDefault() ?? "Synthetic.Tests";
}
