using System.Text.Json;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

internal static class BannedApiConfigurationPolicy
{
    private const string PackageName = "Microsoft.CodeAnalysis.BannedApiAnalyzers";
    private const string BannedSymbolsPath = "../Architecture/BannedSymbols.txt";

    internal static string[] InspectProject(string xml)
    {
        var document = XDocument.Parse(xml, LoadOptions.None);
        var findings = new List<string>();
        var references = document.Descendants("PackageReference")
            .Where(static element => (string?)element.Attribute("Include") == PackageName)
            .ToArray();
        if (references.Length != 1)
        {
            findings.Add($"expected exactly one {PackageName} PackageReference");
        }
        else if ((string?)references[0].Attribute("PrivateAssets") != "all")
        {
            findings.Add($"{PackageName} PackageReference must set PrivateAssets=all");
        }

        var additionalFiles = document.Descendants("AdditionalFiles")
            .Where(static element => (string?)element.Attribute("Include") == BannedSymbolsPath)
            .Count();
        if (additionalFiles != 1)
        {
            findings.Add($"expected exactly one AdditionalFiles include for {BannedSymbolsPath}");
        }

        return findings.ToArray();
    }

    internal static string[] InspectCentralVersion(string xml, string expectedVersion)
    {
        var document = XDocument.Parse(xml, LoadOptions.None);
        var versions = document.Descendants("PackageVersion")
            .Where(static element => (string?)element.Attribute("Include") == PackageName)
            .ToArray();
        if (versions.Length != 1)
        {
            return [$"expected exactly one central version for {PackageName}"];
        }

        var actual = (string?)versions[0].Attribute("Version");
        return actual == expectedVersion
            ? []
            : [$"central {PackageName} version is {actual ?? "missing"}, expected {expectedVersion}"];
    }

    internal static string[] InspectLockFile(string json, string expectedVersion)
    {
        using var document = JsonDocument.Parse(json);
        var findings = new List<string>();
        if (!document.RootElement.TryGetProperty("dependencies", out var dependencies)
            || !dependencies.TryGetProperty("net10.0", out var framework)
            || !framework.TryGetProperty(PackageName, out var package))
        {
            return [$"lock file is missing direct {PackageName} dependency"];
        }

        Expect(package, "type", "Direct", findings);
        Expect(package, "requested", $"[{expectedVersion}, )", findings);
        Expect(package, "resolved", expectedVersion, findings);
        return findings.ToArray();
    }

    private static void Expect(
        JsonElement package,
        string property,
        string expected,
        ICollection<string> findings)
    {
        var actual = package.TryGetProperty(property, out var value) ? value.GetString() : null;
        if (actual != expected)
        {
            findings.Add($"locked {PackageName} {property} is {actual ?? "missing"}, expected {expected}");
        }
    }
}
