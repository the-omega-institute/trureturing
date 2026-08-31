using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

internal sealed record RepositoryIoAccessFinding(string Path, string Api, string Message);
internal sealed record RepositoryIoTestProject(string Project, string Prefix, bool IsExempt);

internal static class RepositoryIoAccessPolicy
{
    internal const string ScribeTestsProject = "StrataLint.Scribe.Tests";
    internal const string ScribeTestsPrefix = "tools/tests/StrataLint.Scribe.Tests/";
    internal const string TemporaryFileSystemPath =
        ScribeTestsPrefix + "Support/TemporaryFileSystem.cs";

    private static readonly IReadOnlySet<string> AuthorizedGatewayPaths =
        new HashSet<string>(StringComparer.Ordinal)
        {
            ScribeTestsPrefix + "Support/RepositoryAccessor.cs",
        };

    private static readonly IReadOnlySet<string> TemporaryGatewayApis =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "System.IO.File.Exists",
            "System.IO.File.ReadAllText",
            "System.IO.File.ReadAllBytes",
            "System.IO.File.WriteAllText",
            "System.IO.File.WriteAllBytes",
            "System.IO.File.AppendAllText",
            "System.IO.File.Delete",
            "System.IO.Directory.CreateDirectory",
            "System.IO.Directory.CreateTempSubdirectory",
            "System.IO.Directory.Exists",
            "System.IO.Directory.GetCurrentDirectory",
            "System.IO.Directory.Delete",
        };

    // InspectRepository scans every test project except these named migration deferrals.
    // The pinned test makes additions review-visible; migration may only remove entries.
    internal static readonly IReadOnlySet<string> DeferredProjectExemptions =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "StrataLint.Tests",
            "StrataLint.ArchitectureTests",
        };

    private static readonly IReadOnlySet<string> PinnedDeferredProjectExemptionBaseline =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "StrataLint.Tests",
            "StrataLint.ArchitectureTests",
        };

    // This syntax policy judges direct calls to the listed repository-I/O primitives in
    // active test projects. It does not judge indirect reads through production loaders,
    // path-shaped reader APIs not listed here, reflection shapes not listed here, or
    // cross-project behavior. Those remain a declared gap, not accessor uniqueness.
    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectRepository(
        string repositoryRoot)
    {
        var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var projects = ClassifyTestProjects(files
            .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => (file.RelativePath, File.ReadAllText(file.FullPath))),
            DeferredProjectExemptions);
        var activePrefixes = projects.Where(static project => !project.IsExempt)
            .Select(static project => project.Prefix).ToArray();

        return files
            .Where(file => activePrefixes.Any(prefix =>
                    file.RelativePath.StartsWith(prefix, StringComparison.Ordinal))
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && !AuthorizedGatewayPaths.Contains(file.RelativePath))
            .SelectMany(file => InspectSource(file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();
    }

    internal static IReadOnlyList<string> FindAddedExemptions(IEnumerable<string> exemptions) =>
        exemptions.Except(PinnedDeferredProjectExemptionBaseline, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

    internal static IReadOnlyList<RepositoryIoTestProject> ClassifyTestProjects(
        IEnumerable<(string RelativePath, string Content)> projects,
        IReadOnlySet<string> exemptions) => projects
        .Where(static project => IsXunitProject(project.Content))
        .Select(project =>
        {
            var name = Path.GetFileNameWithoutExtension(project.RelativePath);
            return new RepositoryIoTestProject(
                name,
                project.RelativePath[..(project.RelativePath.LastIndexOf('/') + 1)],
                exemptions.Contains(name));
        })
        .ToArray();

    private static bool IsXunitProject(string content)
    {
        var document = XDocument.Parse(content, LoadOptions.None);
        return document.Descendants().Any(static element =>
            element.Name.LocalName == "PackageReference"
            && string.Equals((string?)element.Attribute("Include"), "xunit", StringComparison.OrdinalIgnoreCase));
    }

    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectSource(
        string path,
        string source)
    {
        var tree = CSharpSyntaxTree.ParseText(source);
        var root = tree.GetRoot();
        var typedReceivers = TypedIoReceivers(root);
        var findings = tree.GetDiagnostics()
            .Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
            .Select(diagnostic => new RepositoryIoAccessFinding(
                path,
                "UNRECOGNIZED",
                $"unrecognized C# syntax: {diagnostic.GetMessage()}"))
            .ToList();

        foreach (var alias in root.DescendantNodes().OfType<UsingDirectiveSyntax>()
                     .Where(static directive => directive.Alias is not null
                         && directive.Name?.ToString() is "System.IO.File"
                             or "System.IO.Directory"
                             or "System.IO.FileStream"
                             or "System.IO.StreamReader"
                             or "System.IO.StreamWriter"
                             or "System.Xml.Linq.XDocument"
                             or "System.Xml.Linq.XElement"
                             or "System.Xml.XmlReader"
                             or "System.Text.Json.JsonDocument"
                             or "System.AppContext"))
        {
            findings.Add(new RepositoryIoAccessFinding(
                path,
                "UNRECOGNIZED",
                $"line {alias.GetLocation().GetLineSpan().StartLinePosition.Line + 1}: aliases for repository I/O APIs are not recognized"));
        }

        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (invocation.Expression is MemberAccessExpressionSyntax member
                && TryForbiddenStaticApi(member, out var api))
            {
                if (path != TemporaryFileSystemPath
                    || !TemporaryGatewayApis.Contains(api)
                    || RequiresGuardedPath(api) && !HasGuardedFirstArgument(invocation))
                {
                    findings.Add(Finding(path, api, invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
                }
            }
            else if (invocation.Expression is MemberAccessExpressionSyntax reader
                     && TryForbiddenPathReader(reader, invocation, out api))
            {
                findings.Add(Finding(path, api, invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
            else if (invocation.Expression is MemberAccessExpressionSyntax instance
                     && TryForbiddenInstanceApi(instance, typedReceivers, out api))
            {
                findings.Add(Finding(path, api, invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        foreach (var typeOf in root.DescendantNodes().OfType<TypeOfExpressionSyntax>()
                     .Where(static expression => RightmostName(expression.Type) is "File" or "Directory"))
        {
            findings.Add(Finding(
                path,
                $"System.Reflection:System.IO.{RightmostName(typeOf.Type)}",
                typeOf.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
        }

        foreach (var creation in root.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            var type = RightmostName(creation.Type);
            if (type is "FileStream" or "StreamReader" or "StreamWriter")
            {
                findings.Add(Finding(path, $"System.IO.{type}", creation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        foreach (var member in root.DescendantNodes().OfType<MemberAccessExpressionSyntax>())
        {
            if (member.Name.Identifier.ValueText == "BaseDirectory"
                && RightmostName(member.Expression) == "AppContext")
            {
                findings.Add(Finding(path, "System.AppContext.BaseDirectory", member.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        return findings;
    }

    private static bool TryForbiddenStaticApi(MemberAccessExpressionSyntax member, out string api)
    {
        var expression = member.Expression.ToString().Replace("global::", string.Empty, StringComparison.Ordinal);
        var owner = RightmostName(member.Expression);
        if (expression is "File" or "Directory" or "System.IO.File" or "System.IO.Directory")
        {
            api = $"System.IO.{owner}.{member.Name.Identifier.ValueText}";
            return true;
        }

        api = string.Empty;
        return false;
    }

    private static bool RequiresGuardedPath(string api) => api is not
        "System.IO.Directory.CreateTempSubdirectory" and not
        "System.IO.Directory.GetCurrentDirectory";

    private static bool HasGuardedFirstArgument(InvocationExpressionSyntax invocation) =>
        invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is InvocationExpressionSyntax guard
        && guard.Expression is IdentifierNameSyntax identifier
        && identifier.Identifier.ValueText == "EnsureTemporaryPath";

    private static bool TryForbiddenInstanceApi(
        MemberAccessExpressionSyntax member,
        IReadOnlyDictionary<string, string> typedReceivers,
        out string api)
    {
        var method = member.Name.Identifier.ValueText;
        var receiverType = member.Expression switch
        {
            ObjectCreationExpressionSyntax creation => RightmostName(creation.Type),
            IdentifierNameSyntax identifier when typedReceivers.TryGetValue(identifier.Identifier.ValueText, out var type) => type,
            _ => string.Empty,
        };

        if (receiverType == "FileInfo" && FileInfoIoMembers.Contains(method))
        {
            api = $"System.IO.FileInfo.{method}";
            return true;
        }

        if (receiverType == "DirectoryInfo" && DirectoryInfoIoMembers.Contains(method))
        {
            api = $"System.IO.DirectoryInfo.{method}";
            return true;
        }

        var rootReceiver = member.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>().FirstOrDefault();
        if (rootReceiver is not null
            && typedReceivers.TryGetValue(rootReceiver.Identifier.ValueText, out receiverType)
            && receiverType is "IFileSystem" or "FileSystem")
        {
            api = $"System.IO.Abstractions.{receiverType}";
            return true;
        }

        var facadeCreation = member.DescendantNodesAndSelf().OfType<ObjectCreationExpressionSyntax>()
            .FirstOrDefault(static creation => RightmostName(creation.Type) == "FileSystem");
        if (facadeCreation is not null)
        {
            api = "System.IO.Abstractions.FileSystem";
            return true;
        }

        api = string.Empty;
        return false;
    }

    private static readonly IReadOnlySet<string> FileInfoIoMembers =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "OpenRead", "OpenText", "CopyTo",
        };

    private static readonly IReadOnlySet<string> DirectoryInfoIoMembers =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "EnumerateFiles", "GetFiles", "EnumerateFileSystemInfos",
        };

    private static IReadOnlyDictionary<string, string> TypedIoReceivers(SyntaxNode root)
    {
        var receivers = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var parameter in root.DescendantNodes().OfType<ParameterSyntax>())
        {
            var type = parameter.Type is null ? string.Empty : RightmostName(parameter.Type);
            if (type is "FileInfo" or "DirectoryInfo" or "IFileSystem" or "FileSystem")
            {
                receivers[parameter.Identifier.ValueText] = type;
            }
        }

        foreach (var declaration in root.DescendantNodes().OfType<VariableDeclarationSyntax>())
        {
            var type = RightmostName(declaration.Type);
            if (type is "FileInfo" or "DirectoryInfo" or "IFileSystem" or "FileSystem")
            {
                foreach (var variable in declaration.Variables)
                {
                    receivers[variable.Identifier.ValueText] = type;
                }
            }
        }

        return receivers;
    }

    private static bool TryForbiddenPathReader(
        MemberAccessExpressionSyntax member,
        InvocationExpressionSyntax invocation,
        out string api)
    {
        var owner = member.Expression.ToString().Replace("global::", string.Empty, StringComparison.Ordinal);
        var method = member.Name.Identifier.ValueText;
        if (owner is "XDocument" or "System.Xml.Linq.XDocument" && method == "Load")
        {
            api = "System.Xml.Linq.XDocument.Load";
            return true;
        }

        if (owner is "XElement" or "System.Xml.Linq.XElement" && method == "Load")
        {
            api = "System.Xml.Linq.XElement.Load";
            return true;
        }

        if (owner is "XmlReader" or "System.Xml.XmlReader" && method == "Create")
        {
            api = "System.Xml.XmlReader.Create";
            return true;
        }

        if (owner is "JsonDocument" or "System.Text.Json.JsonDocument"
            && method == "Parse"
            && invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression
                is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression))
        {
            api = "System.Text.Json.JsonDocument.Parse";
            return true;
        }

        api = string.Empty;
        return false;
    }

    private static RepositoryIoAccessFinding Finding(string path, string api, int line) => new(
        path,
        api,
        $"line {line}: direct repository I/O is forbidden; use {ScribeTestsProject}.RepositoryAccessor");

    private static string RightmostName(SyntaxNode node) => node switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        _ => string.Empty,
    };
}
