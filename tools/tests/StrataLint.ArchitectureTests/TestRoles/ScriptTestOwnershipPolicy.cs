using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record ScriptOwnershipSource(
    string ProjectPartition,
    string SourcePath,
    string Content);

internal sealed record ScriptOwnershipFinding(
    string Code,
    string Unit,
    string Detail);

internal static class ScriptTestOwnershipPolicy
{
    private const string ScriptProject = "tools/tests/StrataLint.ScriptTests";
    private const string ScriptOwnerRoot = ScriptProject + "/Scripts/";
    private const string MakefileOwnerRoot = ScriptProject + "/Makefiles/";

    internal static IReadOnlyList<ScriptOwnershipFinding> Inspect(
        IReadOnlyList<string> protectedBaseSubjects,
        IReadOnlyList<ScriptOwnershipSource> sources)
    {
        var subjects = protectedBaseSubjects.ToHashSet(StringComparer.Ordinal);
        var units = ParseUnits(sources);
        var findings = new List<ScriptOwnershipFinding>();
        var owners = new List<(string Subject, string Unit)>();

        foreach (var unit in units.Where(static unit => unit.HasTests))
        {
            if (unit.ProjectPartition != ScriptProject)
            {
                if (unit.SubjectDeclarations.Count != 0)
                {
                    findings.Add(new ScriptOwnershipFinding(
                        "SCRIPT-OWNER-PROJECT",
                        unit.Identity,
                        $"script-owned unit must belong to {ScriptProject}"));
                }

                continue;
            }

            if (unit.SubjectDeclarations.Count != 1
                || unit.SubjectDeclarations[0].Subject is not { } subject
                || !subjects.Contains(subject))
            {
                findings.Add(new ScriptOwnershipFinding(
                    "SCRIPT-OWNER-SUBJECT",
                    unit.Identity,
                    "ScriptTests unit must declare exactly one protected-base subject"));
                continue;
            }

            owners.Add((subject, unit.Identity));
            var expectedPath = OwnerPath(subject);
            var actualPath = unit.SubjectDeclarations[0].SourcePath;
            if (!string.Equals(expectedPath, actualPath, StringComparison.Ordinal))
            {
                findings.Add(new ScriptOwnershipFinding(
                    "SCRIPT-OWNER-MIRROR",
                    unit.Identity,
                    $"subject {subject} requires {expectedPath}, found {actualPath}"));
            }
        }

        foreach (var duplicate in owners
                     .GroupBy(static owner => owner.Subject, StringComparer.Ordinal)
                     .Where(static group => group.Count() > 1))
        {
            findings.Add(new ScriptOwnershipFinding(
                "SCRIPT-OWNER-DUPLICATE",
                duplicate.Key,
                $"subject has multiple owner units: {string.Join(", ", duplicate.Select(static owner => owner.Unit).Order(StringComparer.Ordinal))}"));
        }

        return findings
            .OrderBy(static finding => finding.Code, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Unit, StringComparer.Ordinal)
            .ToArray();
    }

    internal static string OwnerPath(string subject)
    {
        if (subject == "Makefile")
        {
            return MakefileOwnerRoot + "RootMakefile.Tests.cs";
        }

        if (subject == "tools/Makefile")
        {
            return MakefileOwnerRoot + "ToolsMakefile.Tests.cs";
        }

        const string Prefix = "tools/scripts/";
        const string Suffix = ".sh";
        if (!subject.StartsWith(Prefix, StringComparison.Ordinal)
            || !subject.EndsWith(Suffix, StringComparison.Ordinal))
        {
            throw new ArgumentException($"Not a script-test subject: {subject}", nameof(subject));
        }

        return ScriptOwnerRoot + subject[Prefix.Length..^Suffix.Length] + ".Tests.cs";
    }

    private static IReadOnlyList<ScriptOwnershipUnit> ParseUnits(
        IEnumerable<ScriptOwnershipSource> sources) => sources
        .SelectMany(ParseFragments)
        .GroupBy(
            static fragment => (fragment.ProjectPartition, fragment.TypeIdentity),
            static fragment => fragment)
        .Select(static group => new ScriptOwnershipUnit(
            $"{group.Key.ProjectPartition}::{group.Key.TypeIdentity}",
            group.Key.ProjectPartition,
            group.Any(static fragment => fragment.HasTests),
            group.SelectMany(static fragment => fragment.SubjectDeclarations).ToArray()))
        .OrderBy(static unit => unit.Identity, StringComparer.Ordinal)
        .ToArray();

    private static IEnumerable<ScriptOwnershipFragment> ParseFragments(
        ScriptOwnershipSource source)
    {
        var root = CSharpSyntaxTree.ParseText(source.Content).GetCompilationUnitRoot();
        foreach (var declaration in root.DescendantNodes().OfType<ClassDeclarationSyntax>())
        {
            var namespaceName = declaration.Ancestors()
                .OfType<BaseNamespaceDeclarationSyntax>()
                .FirstOrDefault()?.Name.ToString();
            var typeIdentity = string.IsNullOrEmpty(namespaceName)
                ? declaration.Identifier.ValueText
                : namespaceName + "." + declaration.Identifier.ValueText;
            var hasTests = declaration.Members
                .OfType<MethodDeclarationSyntax>()
                .Any(static method => method.AttributeLists
                    .SelectMany(static list => list.Attributes)
                    .Any(IsXunitTestAttribute));
            var subjects = declaration.AttributeLists
                .SelectMany(static list => list.Attributes)
                .Where(IsScriptSubjectAttribute)
                .Select(attribute => new ScriptSubjectDeclaration(
                    TrySubject(attribute),
                    source.SourcePath))
                .ToArray();
            yield return new ScriptOwnershipFragment(
                source.ProjectPartition,
                typeIdentity,
                hasTests,
                subjects);
        }
    }

    private static bool IsXunitTestAttribute(AttributeSyntax attribute) =>
        AttributeName(attribute) is "Fact" or "FactAttribute" or "Theory" or "TheoryAttribute";

    private static bool IsScriptSubjectAttribute(AttributeSyntax attribute) =>
        AttributeName(attribute) is "ScriptSubject" or "ScriptSubjectAttribute";

    private static string AttributeName(AttributeSyntax attribute) => attribute.Name switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax aliased => aliased.Name.Identifier.ValueText,
        _ => attribute.Name.ToString(),
    };

    private static string? TrySubject(AttributeSyntax attribute) =>
        attribute.ArgumentList?.Arguments is { Count: 1 } arguments
        && arguments[0].Expression is LiteralExpressionSyntax literal
        && literal.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.StringLiteralExpression)
            ? literal.Token.ValueText.Replace('\\', '/')
            : null;

    private sealed record ScriptOwnershipFragment(
        string ProjectPartition,
        string TypeIdentity,
        bool HasTests,
        IReadOnlyList<ScriptSubjectDeclaration> SubjectDeclarations);

    private sealed record ScriptOwnershipUnit(
        string Identity,
        string ProjectPartition,
        bool HasTests,
        IReadOnlyList<ScriptSubjectDeclaration> SubjectDeclarations);

    private sealed record ScriptSubjectDeclaration(string? Subject, string SourcePath);
}
