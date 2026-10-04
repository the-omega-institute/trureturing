using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using System.Xml.Linq;

namespace StrataLint.Scribe;

internal sealed class ScribeSdkBatch : IDisposable
{
    private readonly string directory;
    private readonly ImmutableArray<(string Entry, string ErrorLog)> projects;

    private ScribeSdkBatch(string directory, ImmutableArray<(string Entry, string ErrorLog)> projects)
    {
        this.directory = directory;
        this.projects = projects;
    }

    internal string ProjectPath => Path.Combine(directory, "batch.proj");

    internal static ScribeSdkBatch Create(string repositoryRoot, ImmutableArray<string> paths)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var configurationPaths = new[] { "Directory.Build.props", ".editorconfig", "Directory.Packages.props", "global.json",
            "tools/Architecture/BannedSymbols.txt", "tools/Architecture/BannedSymbols.Determinism.txt",
            "tools/Architecture/BannedSymbols.Guid.txt" };
        foreach (var path in configurationPaths)
            if (!File.Exists(Path.Combine(root, path)))
                throw new FileNotFoundException("SDK admission configuration is missing: " + path);
        var constants = typeof(ScribeScriptHost).Assembly.GetCustomAttributes<AssemblyMetadataAttribute>()
            .Single(attribute => attribute.Key == "ScribeScriptDefineConstants").Value;
        if (string.IsNullOrWhiteSpace(constants)) throw new InvalidOperationException("Scribe DefineConstants are unavailable");
        var configuration = typeof(ScribeScriptHost).Assembly.GetCustomAttribute<AssemblyConfigurationAttribute>()?.Configuration
            ?? throw new InvalidOperationException("Scribe build configuration is unavailable");
        var runtime = Path.GetDirectoryName(typeof(object).Assembly.Location);
        var references = ScribeScriptHost.ReferenceAssemblies().Select(reference => reference.Display!)
            .Where(path => Path.GetDirectoryName(path) != runtime).ToArray();
        var analyzerMetadata = typeof(ScribeScriptHost).Assembly.GetCustomAttributes<AssemblyMetadataAttribute>()
            .Single(attribute => attribute.Key == "ScribeSdkPackageAnalyzers").Value;
        if (string.IsNullOrWhiteSpace(analyzerMetadata))
            throw new InvalidOperationException("Scribe package analyzers are unavailable");
        var analyzers = analyzerMetadata.Split(';', StringSplitOptions.RemoveEmptyEntries);
        foreach (var analyzer in analyzers)
            if (!File.Exists(analyzer)) throw new FileNotFoundException("SDK admission analyzer is missing: " + analyzer);
        var directory = Path.Combine(root, "build", "scribe-sdk", Path.GetRandomFileName());
        Directory.CreateDirectory(directory);
        var entries = ImmutableArray.CreateBuilder<(string Entry, string ErrorLog)>();
        var projectPaths = new List<string>();
        try
        {
            var nuget = Path.Combine(directory, "NuGet.Config");
            File.WriteAllText(nuget, "<configuration><packageSources><clear /></packageSources></configuration>");
            foreach (var entry in paths)
            {
                var projectDirectory = Path.Combine(directory, projectPaths.Count.ToString(System.Globalization.CultureInfo.InvariantCulture));
                Directory.CreateDirectory(projectDirectory);
                var projectPath = Path.Combine(projectDirectory, "definition.csproj");
                var errorLog = Path.Combine(projectDirectory, "diagnostics.sarif");
                var project = new XElement("Project", new XAttribute("Sdk", "Microsoft.NET.Sdk"),
                    new XElement("PropertyGroup",
                        Property("OutputType", "Library"), Property("EnableDefaultCompileItems", "false"),
                        Property("RootNamespace", "StrataLint.Scribe.Documents"),
                        Property("Configuration", configuration), Property("DefineConstants", constants),
                        Property("DisableImplicitFrameworkDefines", "true"), Property("DisableImplicitConfigurationDefines", "true"),
                        Property("Features", "$(Features);experimental-data-section-string-literals=100"),
                        Property("RestoreLockedMode", "true"), Property("NuGetAudit", "false"),
                        Property("RestoreConfigFile", nuget), Property("ErrorLog", errorLog + ",version=2.1")),
                    new XElement("ItemGroup",
                        new XElement("Compile", new XAttribute("Include", Path.Combine(root, entry)))),
                    new XElement("ItemGroup", references.Select(path => new XElement("Reference",
                        new XAttribute("Include", Path.GetFileNameWithoutExtension(path)),
                        new XElement("HintPath", path), new XElement("Private", "false")))),
                    new XElement("ItemGroup", analyzers.Select(path =>
                        new XElement("Analyzer", new XAttribute("Include", path)))),
                    new XElement("ItemGroup", configurationPaths.Where(path => path.StartsWith("tools/Architecture/", StringComparison.Ordinal))
                        .Select(path => new XElement("AdditionalFiles", new XAttribute("Include", Path.Combine(root, path))))));
                project.Save(projectPath);
                File.WriteAllText(Path.Combine(projectDirectory, "packages.lock.json"),
                    "{\"version\":1,\"dependencies\":{\"net10.0\":{}}}");
                projectPaths.Add(projectPath);
                entries.Add((entry, errorLog));
            }
            var batch = new ScribeSdkBatch(directory, entries.ToImmutable());
            new XElement("Project",
                new XElement("ItemGroup", projectPaths.Select(path => new XElement("DefinitionProject", new XAttribute("Include", path)))),
                new XElement("Target", new XAttribute("Name", "Restore"), BuildTask("Restore", configuration)),
                new XElement("Target", new XAttribute("Name", "Build"), new XAttribute("DependsOnTargets", "Restore"), BuildTask("Build", configuration)))
                .Save(batch.ProjectPath);
            return batch;
        }
        catch
        {
            Directory.Delete(directory, recursive: true);
            throw;
        }
    }

    internal ImmutableArray<ScribeSdkDiagnostic> ReadDiagnostics()
    {
        var diagnostics = ImmutableArray.CreateBuilder<ScribeSdkDiagnostic>();
        foreach (var (entry, log) in projects)
        {
            if (!File.Exists(log)) continue;
            using var json = JsonDocument.Parse(File.ReadAllBytes(log));
            foreach (var run in json.RootElement.GetProperty("runs").EnumerateArray())
            foreach (var result in run.GetProperty("results").EnumerateArray())
            {
                if (result.GetProperty("level").GetString() != "error") continue;
                if (result.TryGetProperty("suppressions", out var suppressions)
                    && suppressions.EnumerateArray().Any(suppression =>
                        !suppression.TryGetProperty("status", out var status) || status.GetString() == "accepted"))
                    continue;
                var location = result.TryGetProperty("locations", out var locations) && locations.GetArrayLength() > 0
                    ? locations[0].GetProperty("physicalLocation") : default;
                var source = location.ValueKind == JsonValueKind.Undefined ? entry
                    : location.GetProperty("artifactLocation").GetProperty("uri").GetString()!;
                if (Uri.TryCreate(source, UriKind.Absolute, out var uri) && uri.IsFile) source = uri.LocalPath;
                if (location.ValueKind != JsonValueKind.Undefined && location.TryGetProperty("region", out var region))
                    source += FormattableString.Invariant($"({region.GetProperty("startLine").GetInt32()},{region.GetProperty("startColumn").GetInt32()})");
                diagnostics.Add(new(entry, result.GetProperty("ruleId").GetString()!, source,
                    result.GetProperty("message").GetProperty("text").GetString()!));
            }
        }
        return diagnostics.Distinct().OrderBy(diagnostic => diagnostic.DefinitionPath, StringComparer.Ordinal)
            .ThenBy(diagnostic => diagnostic.Location, StringComparer.Ordinal).ThenBy(diagnostic => diagnostic.Id, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static XElement Property(string name, string value) => new(name, value);
    private static XElement BuildTask(string target, string configuration) => new("MSBuild",
        new XAttribute("Projects", "@(DefinitionProject)"), new XAttribute("Targets", target),
        new XAttribute("Properties", "Configuration=" + configuration),
        new XAttribute("BuildInParallel", "true"), new XAttribute("StopOnFirstFailure", "false"));

    public void Dispose() => Directory.Delete(directory, recursive: true);
}
