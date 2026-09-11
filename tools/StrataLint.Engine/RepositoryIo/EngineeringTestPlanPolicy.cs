using System.Collections.Immutable;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal static class EngineeringTestPlanPolicy
{
    internal static ImmutableArray<string> Evaluate(TestProjectTopologySnapshot candidate) =>
        candidate.Projects.Where(IsTestProject)
            .Select(static project => project.Path)
            // The script suite remains locally runnable but was retired from CI on 2026-09-07.
            .Where(static path => path != "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj")
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

    private static bool IsTestProject(TestProjectTopologyProject project)
    {
        var document = XDocument.Parse(project.Content, LoadOptions.None);
        var declarations = document.Descendants()
            .Where(static element => element.Name.LocalName == "IsTestProject")
            .Select(static element => element.Value.Trim())
            .Distinct(StringComparer.OrdinalIgnoreCase)
            .ToArray();
        // Explicit false excludes xUnit-based support libraries (#5516).
        return declarations switch
        {
            [] => document.Descendants().Any(static element =>
                element.Name.LocalName == "PackageReference"
                && string.Equals(
                    (string?)element.Attribute("Include"),
                    "xunit",
                    StringComparison.OrdinalIgnoreCase)),
            [var value] when value.Equals("true", StringComparison.OrdinalIgnoreCase) => true,
            [var value] when value.Equals("false", StringComparison.OrdinalIgnoreCase) => false,
            _ => throw new InvalidDataException(
                $"project has no unambiguous literal IsTestProject classification: {project.Path}"),
        };
    }
}
