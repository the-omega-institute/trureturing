using System.Text.Json;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

internal static class BannedApiConfigurationPolicy
{
    private const string PackageName = "Microsoft.CodeAnalysis.BannedApiAnalyzers";
    private const string BannedSymbolsPath = "../Architecture/BannedSymbols.txt";
    private const string DeterminismBannedSymbolsPath =
        "../Architecture/BannedSymbols.Determinism.txt";
    private const string GuidBannedSymbolsPath = "../Architecture/BannedSymbols.Guid.txt";

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

    internal static string[] InspectDeterminismProject(string xml)
    {
        var document = XDocument.Parse(xml, LoadOptions.None);
        var count = document.Descendants("AdditionalFiles")
            .Count(static element =>
                (string?)element.Attribute("Include") == DeterminismBannedSymbolsPath);
        return count == 1
            ? []
            : [$"expected exactly one AdditionalFiles include for {DeterminismBannedSymbolsPath}"];
    }

    internal static string[] InspectGuidProject(string xml)
    {
        var document = XDocument.Parse(xml, LoadOptions.None);
        var count = document.Descendants("AdditionalFiles")
            .Count(static element =>
                (string?)element.Attribute("Include") == GuidBannedSymbolsPath);
        return count == 1
            ? []
            : [$"expected exactly one AdditionalFiles include for {GuidBannedSymbolsPath}"];
    }

    internal static string ReadCentralVersion(string xml)
    {
        var document = XDocument.Parse(xml, LoadOptions.None);
        var versions = document.Descendants("PackageVersion")
            .Where(static element => (string?)element.Attribute("Include") == PackageName)
            .ToArray();
        if (versions.Length != 1
            || (string?)versions[0].Attribute("Version") is not { Length: > 0 } version)
        {
            throw new FormatException($"expected exactly one central version for {PackageName}");
        }

        return version;
    }

    internal static string[] InspectLockFile(string json, string expectedVersion)
    {
        using var document = JsonDocument.Parse(json);
        var findings = new List<string>();
        if (!document.RootElement.TryGetProperty("dependencies", out var dependencies)
            || dependencies.ValueKind != JsonValueKind.Object)
        {
            return ["lock file is missing framework dependencies"];
        }

        var frameworks = dependencies.EnumerateObject().ToArray();
        if (frameworks.Length == 0)
        {
            return ["lock file is missing framework dependencies"];
        }

        foreach (var framework in frameworks)
        {
            if (!framework.Value.TryGetProperty(PackageName, out var package))
            {
                findings.Add(
                    $"lock file framework {framework.Name} is missing direct {PackageName} dependency");
                continue;
            }

            Expect(package, "type", "Direct", findings);
            Expect(package, "requested", $"[{expectedVersion}, )", findings);
            Expect(package, "resolved", expectedVersion, findings);
        }

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
