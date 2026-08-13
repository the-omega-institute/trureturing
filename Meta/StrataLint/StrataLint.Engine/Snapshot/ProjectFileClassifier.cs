using System.Xml.Linq;

namespace StrataLint.Engine;

internal static class ProjectFileClassifier
{
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
}
