using System.Xml.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record CentralPackageVersionLiteralFinding(
    string Path,
    string Value,
    string Message);

internal static class CentralPackageVersionLiteralPolicy
{
    internal static IReadOnlyList<CentralPackageVersionLiteralFinding> InspectRepository(
        string repositoryRoot)
    {
        var versions = LoadVersions(File.ReadAllText(
            Path.Combine(repositoryRoot, "Directory.Packages.props")));
        return CSharpRepositorySources.Enumerate(repositoryRoot)
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath),
                versions))
            .ToArray();
    }

    internal static IReadOnlySet<string> LoadVersions(string xml)
    {
        var versions = XDocument.Parse(xml, LoadOptions.None)
            .Descendants("PackageVersion")
            .Select(static element => (string?)element.Attribute("Version"))
            .ToArray();
        if (versions.Length == 0 || versions.Any(static version => string.IsNullOrEmpty(version)))
        {
            throw new FormatException(
                "Directory.Packages.props must define nonempty central package versions");
        }

        return versions.OfType<string>().ToHashSet(StringComparer.Ordinal);
    }

    internal static IReadOnlyList<CentralPackageVersionLiteralFinding> InspectSource(
        string path,
        string source,
        IReadOnlySet<string> centralVersions)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return root.DescendantNodes()
            .OfType<LiteralExpressionSyntax>()
            .Where(static literal => literal.IsKind(SyntaxKind.StringLiteralExpression))
            .Where(literal => centralVersions.Contains(literal.Token.ValueText))
            .Select(literal => new CentralPackageVersionLiteralFinding(
                path,
                literal.Token.ValueText,
                $"C# string literal copies central package version {literal.Token.ValueText}; read Directory.Packages.props instead"))
            .ToArray();
    }
}
