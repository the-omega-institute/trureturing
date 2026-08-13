using System.Xml.Linq;

namespace StrataLint.Tests;

// Test-only project classification stays with the tests that consume it, not in Engine.
public static class ProjectFileClassifier
{
    public static bool IsXunitProject(string content)
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
