using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

internal sealed record NamespaceFinding(string Path, string Message);

internal static partial class NamespacePolicy
{
    internal static NamespaceFinding[] InspectRepository(string repositoryRoot)
    {
        var findings = new List<NamespaceFinding>();
        var metaRoot = Path.Combine(repositoryRoot, "Meta", "StrataLint");
        foreach (var path in Directory.EnumerateFiles(metaRoot, "*.cs", SearchOption.AllDirectories)
                     .Where(static path => !IsBuildOutput(path)))
        {
            var project = FindProject(path, metaRoot);
            if (project is null)
            {
                findings.Add(new NamespaceFinding(
                    Relative(repositoryRoot, path),
                    "C# source is not owned by a project directory."));
                continue;
            }

            var rootNamespace = XDocument.Load(project)
                .Descendants("RootNamespace")
                .Select(static element => element.Value)
                .Single();
            findings.AddRange(Check(
                Relative(repositoryRoot, path),
                rootNamespace,
                File.ReadAllText(path),
                AllowsGlobalNamespace(path, project)));
        }

        var blueprintRoot = Path.Combine(repositoryRoot, "Blueprint");
        foreach (var path in Directory.EnumerateFiles(
                     blueprintRoot, "*.scribe.cs", SearchOption.AllDirectories))
        {
            var directory = Path.GetDirectoryName(Path.GetRelativePath(blueprintRoot, path))
                ?? throw new InvalidOperationException("Blueprint source has no directory.");
            var expected = "StrataLint.Scribe.Blueprint."
                + directory.Replace(Path.DirectorySeparatorChar, '.');
            findings.AddRange(Check(
                Relative(repositoryRoot, path),
                expected,
                File.ReadAllText(path),
                allowGlobalNamespace: false));
        }

        return findings.OrderBy(static item => item.Path, StringComparer.Ordinal).ToArray();
    }

    internal static NamespaceFinding[] Check(
        string path,
        string expected,
        string source,
        bool allowGlobalNamespace = false)
    {
        var declarations = NamespaceDeclaration().Matches(source)
            .Select(static match => match.Groups[1].Value)
            .ToArray();
        if (declarations.Length == 0 && allowGlobalNamespace)
        {
            return [];
        }

        if (declarations.Length != 1)
        {
            return [new NamespaceFinding(path, "source must declare exactly one namespace")];
        }

        return string.Equals(declarations[0], expected, StringComparison.Ordinal)
            ? []
            : [new NamespaceFinding(
                path,
                $"namespace {declarations[0]} does not match {expected}")];
    }

    private static string? FindProject(string path, string metaRoot)
    {
        for (var current = Directory.GetParent(path); current is not null; current = current.Parent)
        {
            var project = Directory.EnumerateFiles(current.FullName, "*.csproj").SingleOrDefault();
            if (project is not null)
            {
                return project;
            }

            if (string.Equals(current.FullName, metaRoot, StringComparison.Ordinal))
            {
                return null;
            }
        }

        return null;
    }

    private static bool AllowsGlobalNamespace(string path, string project) =>
        Path.GetFileName(path) is "AssemblyInfo.cs" or "Usings.cs"
        || (Path.GetFileName(path) == "Program.cs"
            && Path.GetFileName(Path.GetDirectoryName(project)) == "StrataLint.Scribe");

    private static bool IsBuildOutput(string path) =>
        path.Split(Path.DirectorySeparatorChar)
            .Any(static part => part is "bin" or "obj");

    private static string Relative(string repositoryRoot, string path) =>
        Path.GetRelativePath(repositoryRoot, path).Replace(Path.DirectorySeparatorChar, '/');

    [GeneratedRegex(
        @"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:;|\{)",
        RegexOptions.Multiline | RegexOptions.CultureInvariant)]
    private static partial Regex NamespaceDeclaration();
}
