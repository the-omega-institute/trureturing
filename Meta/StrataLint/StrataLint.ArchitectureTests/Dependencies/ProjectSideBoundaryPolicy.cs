using System.Xml;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

internal sealed record ProjectManifest(string Path, string Content);

internal enum ProjectBoundaryViolation
{
    SourceCrossesSide,
    ToolReferencesContent,
}

internal sealed record ProjectSideBoundaryFinding(
    ProjectBoundaryViolation Kind,
    string Message);

internal static class ProjectSideBoundaryPolicy
{
    private static readonly IReadOnlySet<string> SourceItemNames =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "Compile",
            "Content",
            "None",
            "EmbeddedResource",
            "AdditionalFiles",
        };

    internal static IReadOnlyList<ProjectSideBoundaryFinding> Inspect(
        IEnumerable<ProjectManifest> manifests)
    {
        var findings = new List<ProjectSideBoundaryFinding>();
        foreach (var manifest in manifests)
        {
            var document = XDocument.Parse(manifest.Content, LoadOptions.SetLineInfo);
            var projectIsTool = IsToolPath(manifest.Path);
            foreach (var item in document.Descendants())
            {
                var include = (string?)item.Attribute("Include");
                if (include is null)
                {
                    continue;
                }

                foreach (var value in include.Split(';', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
                {
                    var normalized = NormalizeInclude(manifest.Path, value);
                    if (SourceItemNames.Contains(item.Name.LocalName)
                        && IsToolPath(normalized) != projectIsTool)
                    {
                        findings.Add(Finding(
                            ProjectBoundaryViolation.SourceCrossesSide,
                            manifest.Path,
                            item,
                            value,
                            normalized));
                    }
                    else if (item.Name.LocalName == "ProjectReference"
                             && projectIsTool
                             && !IsToolPath(normalized))
                    {
                        findings.Add(Finding(
                            ProjectBoundaryViolation.ToolReferencesContent,
                            manifest.Path,
                            item,
                            value,
                            normalized));
                    }
                }
            }
        }

        return findings;
    }

    private static ProjectSideBoundaryFinding Finding(
        ProjectBoundaryViolation kind,
        string project,
        XElement item,
        string include,
        string normalized)
    {
        var line = (item as IXmlLineInfo)?.HasLineInfo() == true
            ? $":{((IXmlLineInfo)item).LineNumber}"
            : string.Empty;
        return new ProjectSideBoundaryFinding(
            kind,
            $"{project}{line}: {item.Name.LocalName} Include=\"{include}\" resolves to {normalized}");
    }

    private static bool IsToolPath(string path) =>
        path.StartsWith("Meta/StrataLint/", StringComparison.Ordinal);

    private static string NormalizeInclude(string projectPath, string include)
    {
        var segments = new List<string>();
        var projectDirectory = projectPath[..projectPath.LastIndexOf('/')];
        AppendSegments(segments, projectDirectory);
        AppendSegments(segments, include.Replace('\\', '/'));
        return string.Join('/', segments);
    }

    private static void AppendSegments(List<string> normalized, string path)
    {
        foreach (var segment in path.Split('/', StringSplitOptions.RemoveEmptyEntries))
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
    }
}
