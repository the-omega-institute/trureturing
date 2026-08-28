using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal static partial class SelfTestGovernancePolicy
{
    private const string PackageName = "Microsoft.CodeAnalysis.BannedApiAnalyzers";
    private const string BannedSymbolsPath = "../Architecture/BannedSymbols.txt";
    private const string DeterminismBannedSymbolsPath =
        "../Architecture/BannedSymbols.Determinism.txt";
    private const string GuidBannedSymbolsPath = "../Architecture/BannedSymbols.Guid.txt";

    private static readonly string[] NumericTypes =
    [
        "System.Byte",
        "System.SByte",
        "System.Int16",
        "System.UInt16",
        "System.Int32",
        "System.UInt32",
        "System.Int64",
        "System.UInt64",
        "System.Int128",
        "System.UInt128",
        "System.Half",
        "System.Single",
        "System.Double",
        "System.Decimal",
    ];

    internal static IReadOnlyList<string> RequiredAmbientRuntimeMembers { get; } =
    [
        "P:System.DateTime.Now",
        "P:System.DateTime.UtcNow",
        "P:System.DateTimeOffset.Now",
        "P:System.DateTimeOffset.UtcNow",
        "T:System.Random",
        "P:System.Environment.TickCount",
        "P:System.Environment.TickCount64",
        "M:System.Threading.Thread.Sleep(System.Int32)",
        "M:System.Threading.Thread.Sleep(System.TimeSpan)",
        "M:System.Threading.Tasks.Task.Delay(System.Int32)",
        "M:System.Threading.Tasks.Task.Delay(System.Int32,System.Threading.CancellationToken)",
        "M:System.Threading.Tasks.Task.Delay(System.TimeSpan)",
        "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.Threading.CancellationToken)",
        "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider)",
        "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider,System.Threading.CancellationToken)",
        "T:System.Diagnostics.Stopwatch",
    ];

    internal static string[] InspectRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var findings = new List<string>();
        findings.AddRange(InspectTower(File.ReadAllText(
            Path.Combine(repositoryRoot, RepositoryRules.TowerManifestPath))));

        var centralVersion = ReadBannedApiVersion(File.ReadAllText(
            Path.Combine(repositoryRoot, "Directory.Packages.props")));
        foreach (var (projectName, requireGuid) in new[]
                 {
                     ("StrataLint.Engine", true),
                     ("StrataLint.Scribe", true),
                     ("StrataLint.Cli", false),
                 })
        {
            var directory = Path.Combine(repositoryRoot, "tools", projectName);
            findings.AddRange(InspectBannedApiProject(
                    File.ReadAllText(Path.Combine(directory, projectName + ".csproj")),
                    requireGuid)
                .Select(finding => $"{projectName}: {finding}"));
            findings.AddRange(InspectBannedApiLock(
                    File.ReadAllText(Path.Combine(directory, "packages.lock.json")),
                    centralVersion)
                .Select(finding => $"{projectName}: {finding}"));
        }

        findings.AddRange(InspectBannedSymbols(
            File.ReadAllText(Path.Combine(repositoryRoot, "tools/Architecture/BannedSymbols.txt")),
            File.ReadAllText(Path.Combine(
                repositoryRoot, "tools/Architecture/BannedSymbols.Determinism.txt")),
            File.ReadAllText(Path.Combine(
                repositoryRoot, "tools/Architecture/BannedSymbols.Guid.txt"))));
        findings.AddRange(InspectToolsNamespaces(repositoryRoot));
        return findings.Order(StringComparer.Ordinal).ToArray();
    }

    internal static string[] InspectTower(string yaml)
    {
        var loaded = TowerManifestParser.Parse(System.Text.Encoding.UTF8.GetBytes(yaml));
        if (loaded is TowerManifestParseOutcome.Invalid invalid)
        {
            return ["TOWER: " + invalid.Message];
        }

        var components = ((TowerManifestParseOutcome.Loaded)loaded).Syntax.Components;
        var architecture = components
            .Where(static component => component.Id == "csharp-architecture")
            .ToArray();
        if (architecture.Length != 1)
        {
            return ["TOWER: expected exactly one csharp-architecture component"];
        }

        string[] expectedJudges =
            ["architecture-tests", "banned-api-analyzers", "engineering-ci"];
        var findings = new List<string>();
        if (!architecture[0].JudgedBy.SequenceEqual(expectedJudges, StringComparer.Ordinal))
        {
            findings.Add("TOWER: csharp-architecture judged_by chain is not canonical");
        }

        if (architecture[0].Verification != "verified")
        {
            findings.Add("TOWER: csharp-architecture verification must be verified");
        }

        return findings.ToArray();
    }

    internal static string[] InspectBannedApiProject(string xml, bool requireGuidDenylist)
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

        RequireAdditionalFile(document, BannedSymbolsPath, findings);
        RequireAdditionalFile(document, DeterminismBannedSymbolsPath, findings);
        if (requireGuidDenylist)
        {
            RequireAdditionalFile(document, GuidBannedSymbolsPath, findings);
        }
        else if (document.Descendants("AdditionalFiles").Any(static element =>
                     (string?)element.Attribute("Include") == GuidBannedSymbolsPath))
        {
            findings.Add($"CLI must not include {GuidBannedSymbolsPath}");
        }

        return findings.ToArray();
    }

    internal static string ReadBannedApiVersion(string xml)
    {
        var versions = XDocument.Parse(xml, LoadOptions.None)
            .Descendants("PackageVersion")
            .Where(static element => (string?)element.Attribute("Include") == PackageName)
            .ToArray();
        if (versions.Length != 1
            || (string?)versions[0].Attribute("Version") is not { Length: > 0 } version)
        {
            throw new FormatException($"expected exactly one central version for {PackageName}");
        }

        return version;
    }

    internal static string[] InspectBannedApiLock(string json, string expectedVersion)
    {
        using var document = JsonDocument.Parse(json);
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

        var findings = new List<string>();
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

    internal static string[] InspectBannedSymbols(
        string cultureText,
        string determinismText,
        string guidText)
    {
        var findings = new List<string>();
        RequireExactSymbols(
            "BannedSymbols.txt",
            RequiredCultureSensitiveMembers(),
            ParseSymbols(cultureText),
            findings);
        RequireExactSymbols(
            "BannedSymbols.Determinism.txt",
            RequiredAmbientRuntimeMembers,
            ParseSymbols(determinismText),
            findings);
        RequireExactSymbols(
            "BannedSymbols.Guid.txt",
            ["M:System.Guid.NewGuid"],
            ParseSymbols(guidText),
            findings);
        return findings.ToArray();
    }

    internal static IEnumerable<string> RequiredCultureSensitiveMembers()
    {
        foreach (var type in NumericTypes)
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.Parse(System.String,System.Globalization.NumberStyles)";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Byte}},{type}@)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
        }

        const string bigInteger = "System.Numerics.BigInteger";
        yield return $"M:{bigInteger}.Parse(System.String)";
        yield return $"M:{bigInteger}.Parse(System.String,System.Globalization.NumberStyles)";
        yield return $"M:{bigInteger}.ToString";
        yield return $"M:{bigInteger}.ToString(System.String)";
        yield return $"M:{bigInteger}.TryParse(System.ReadOnlySpan{{System.Char}},{bigInteger}@)";
        yield return $"M:{bigInteger}.TryParse(System.String,{bigInteger}@)";

        foreach (var type in new[] { "System.DateTime", "System.DateTimeOffset", "System.TimeSpan" })
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
        }

        foreach (var type in new[] { "System.DateOnly", "System.TimeOnly" })
        {
            yield return $"M:{type}.Parse(System.String)";
            yield return $"M:{type}.ParseExact(System.ReadOnlySpan{{System.Char}},System.String[])";
            yield return $"M:{type}.ParseExact(System.String,System.String)";
            yield return $"M:{type}.ParseExact(System.String,System.String[])";
            yield return $"M:{type}.ToString";
            yield return $"M:{type}.ToString(System.String)";
            yield return $"M:{type}.TryParse(System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParse(System.String,{type}@)";
            yield return $"M:{type}.TryParseExact(System.ReadOnlySpan{{System.Char}},System.ReadOnlySpan{{System.Char}},{type}@)";
            yield return $"M:{type}.TryParseExact(System.ReadOnlySpan{{System.Char}},System.String[],{type}@)";
            yield return $"M:{type}.TryParseExact(System.String,System.String,{type}@)";
            yield return $"M:{type}.TryParseExact(System.String,System.String[],{type}@)";
        }
    }

    internal static string[] CheckToolsNamespace(
        string path,
        string expected,
        string source,
        bool allowGlobalNamespace = false)
    {
        var declarations = NamespaceDeclaration().Matches(source)
            .Select(static match => match.Groups[1].Value)
            .ToArray();
        if (declarations.Length == 0 && allowGlobalNamespace)
        {
            return [];
        }

        if (declarations.Length != 1)
        {
            return [$"{path}: source must declare exactly one namespace"];
        }

        return declarations[0] == expected
            ? []
            : [$"{path}: namespace {declarations[0]} does not match {expected}"];
    }

    private static IEnumerable<string> InspectToolsNamespaces(string repositoryRoot)
    {
        var toolsRoot = Path.Combine(repositoryRoot, "tools");
        foreach (var path in Directory.EnumerateFiles(toolsRoot, "*.cs", SearchOption.AllDirectories)
                     .Where(static path => !IsBuildOutput(path))
                     .Order(StringComparer.Ordinal))
        {
            var project = FindProject(path, toolsRoot);
            var relative = Path.GetRelativePath(repositoryRoot, path)
                .Replace(Path.DirectorySeparatorChar, '/');
            if (project is null)
            {
                yield return $"{relative}: C# source is not owned by a project directory";
                continue;
            }

            var roots = XDocument.Load(project)
                .Descendants("RootNamespace")
                .Select(static element => element.Value)
                .ToArray();
            if (roots.Length != 1)
            {
                yield return $"{relative}: owning project must declare exactly one RootNamespace";
                continue;
            }

            foreach (var finding in CheckToolsNamespace(
                         relative,
                         roots[0],
                         File.ReadAllText(path),
                         AllowsGlobalNamespace(path, project)))
            {
                yield return finding;
            }
        }
    }

    private static void RequireAdditionalFile(
        XDocument document,
        string path,
        ICollection<string> findings)
    {
        var count = document.Descendants("AdditionalFiles")
            .Count(element => (string?)element.Attribute("Include") == path);
        if (count != 1)
        {
            findings.Add($"expected exactly one AdditionalFiles include for {path}");
        }
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

    private static string[] ParseSymbols(string text) => text
        .Split('\n')
        .Select(static line => line.TrimEnd('\r'))
        .Where(static line => !string.IsNullOrWhiteSpace(line))
        .Select(static line => line.Split(';', 2)[0])
        .ToArray();

    private static void RequireExactSymbols(
        string label,
        IEnumerable<string> expected,
        IEnumerable<string> actual,
        ICollection<string> findings)
    {
        var expectedSet = expected.Order(StringComparer.Ordinal).ToArray();
        var actualSet = actual.Order(StringComparer.Ordinal).ToArray();
        if (!expectedSet.SequenceEqual(actualSet, StringComparer.Ordinal))
        {
            findings.Add($"{label}: symbol matrix is not canonical");
        }
    }

    private static string? FindProject(string path, string toolsRoot)
    {
        for (var current = Directory.GetParent(path); current is not null; current = current.Parent)
        {
            var projects = Directory.EnumerateFiles(current.FullName, "*.csproj")
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (projects.Length > 1)
            {
                throw new FormatException($"multiple project owners for {path}");
            }

            if (projects.Length == 1)
            {
                return projects[0];
            }

            if (current.FullName == toolsRoot)
            {
                return null;
            }
        }

        return null;
    }

    private static bool AllowsGlobalNamespace(string path, string project) =>
        Path.GetFileName(path) is "AssemblyInfo.cs" or "Usings.cs"
        || (Path.GetFileName(path) == "Program.cs"
            && Path.GetFileName(Path.GetDirectoryName(project)) == "StrataLint.Scribe");

    private static bool IsBuildOutput(string path) =>
        path.Split(Path.DirectorySeparatorChar).Any(static part => part is "bin" or "obj");

    [GeneratedRegex(
        @"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:;|\{)",
        RegexOptions.Multiline | RegexOptions.CultureInvariant)]
    private static partial Regex NamespaceDeclaration();
}
