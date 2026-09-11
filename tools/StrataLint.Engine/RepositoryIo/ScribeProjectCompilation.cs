using System.Xml.Linq;

namespace StrataLint.Engine;

// The remaining engineering project classifier is replaced by the project-registration layer.
internal static class ScribeProjectCompilationContext
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
