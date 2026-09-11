using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    // This describes the running managed process and declared SDK, not installed host
    // dependencies. The same function supplies tests, common stages and downstream readers.
    internal static string ExecutionEnvironment(string root)
    {
        var os = OperatingSystem.IsMacOS() ? "macos" : OperatingSystem.IsLinux() ? "linux"
            : OperatingSystem.IsWindows() ? "windows" : throw new InvalidDataException("unsupported execution OS");
        var arch = RuntimeInformation.ProcessArchitecture.ToString().ToLowerInvariant();
        if (arch is not ("arm64" or "x64")) throw new InvalidDataException("unsupported execution architecture: " + arch);
        using var config = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "global.json")));
        var sdk = config.RootElement.GetProperty("sdk").GetProperty("version").GetString();
        if (string.IsNullOrWhiteSpace(sdk)) throw new InvalidDataException("missing declared execution SDK: global.json");
        return JsonSerializer.Serialize(new { os, arch, sdk, runtime = Environment.Version.ToString(),
            options = "Release;no-build;no-restore;unfiltered;trx;language=en-US;CI=true", processors = Environment.GetEnvironmentVariable("DOTNET_PROCESSOR_COUNT") });
    }

    internal static IReadOnlyDictionary<string, string> CheckInputFingerprints(string root, RepositorySnapshot snapshot, bool currentReport = false, IReadOnlyCollection<string>? selectedIds = null)
    {
        var files = snapshot.Files.Values.Select(item => new EngineeringSource(item.Path.Value, item.Text)).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        var checks = ReadCheckManifest(snapshot, registry).Where(check => selectedIds is null || selectedIds.Contains(check.Id)).ToArray();
        var sources = registry.Sources(files);
        var paths = snapshot.Files.Keys.Select(path => path.Value).ToArray();
        var projects = registry.Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var environment = ExecutionEnvironment(root);
        string? reportValue = null;
        if (currentReport && checks.Any(check => check.ReportInputs.Length != 0))
        {
            _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
            reportValue = Hash(Path.Combine(root, ReportPath));
        }
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var check in checks)
        {
            var selected = new HashSet<string>(StringComparer.Ordinal);
            foreach (var project in check.ProgramProjects) Add(project);
            var materialPaths = EngineeringProjectRegistry.ExpandInputs(paths, check.Materials, check.MaterialExcludes, check.Id).ToHashSet(StringComparer.Ordinal);
            foreach (var report in check.ReportInputs)
            {
                materialPaths.UnionWith(EngineeringProjectRegistry.ExpandInputs(paths, report.Materials, [], check.Id));
                var producer = ReadProducer(snapshot, report.Producer);
                foreach (var project in producer.Projects) Add(project);
                materialPaths.UnionWith(producer.Scripts.Concat(producer.Materials));
                materialPaths.Add(report.Producer);
            }
            foreach (var project in selected.Select(path => projects[path]))
            {
                materialPaths.Add(project.Path);
                materialPaths.UnionWith(sources[project.Path].Select(source => source.Path));
                materialPaths.UnionWith(EngineeringProjectRegistry.ExpandInputs(paths, project.BuildInputs!, [], project.Path));
            }
            object ProjectProjection(EngineeringProjectRegistration project) => new
            {
                project.Path, project.Assembly, include = project.Include.Order(StringComparer.Ordinal),
                exclude = project.Exclude.Order(StringComparer.Ordinal), references = project.References.Order(StringComparer.Ordinal),
                build_inputs = project.BuildInputs!.Order(StringComparer.Ordinal),
                // Only governance selftest consumes namespace policy. These fields never
                // enter the compiler/producer five-field registration projection.
                governance = check.Id == "selftest-pair" ? new { project.Role, project.Ci, project.Owner, project.OwnedTestAssembly, project.TestPartition, project.RootNamespace,
                    project.NamespaceExclude, project.GlobalNamespaceExceptions } : null,
            };
            object Material(string path)
            {
                var item = snapshot.Files[RepoPath.CreateKnown(path)];
                var executable = !OperatingSystem.IsWindows() && (File.GetUnixFileMode(Path.Combine(root, path))
                    & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0;
                return new { path, mode = executable ? "executable" : "regular", sha256 = Convert.ToHexStringLower(SHA256.HashData(item.RawBytes.AsSpan())) };
            }
            result.Add(check.Id, Digest(new { contract = "common-check-execution-v2", registration = check,
                projects = selected.Order(StringComparer.Ordinal).Select(name => ProjectProjection(projects[name])),
                materials = materialPaths.Order(StringComparer.Ordinal).Select(Material),
                inventory = EngineeringProjectRegistry.ExpandInputs(paths, check.PathInventory, [], check.Id),
                report = check.ReportInputs.Length == 0 ? null : reportValue, environment }));
            void Add(string path)
            {
                if (!projects.TryGetValue(path, out var project)) throw new InvalidDataException($"check {check.Id} references unregistered project: {path}");
                if (!selected.Add(path)) return;
                foreach (var reference in project.References) Add(reference);
            }
        }
        foreach (var check in checks.Where(UsesScribe))
            result[check.Id] = Digest(new { input = result[check.Id], scribe = result["scribe-describe"] });
        return result;
    }

    private sealed record CheckProducer(string Schema, string[] Scripts, string[] Projects, string[] Materials);
    private static CheckProducer ReadProducer(RepositorySnapshot snapshot, string path)
    {
        try
        {
            var producer = JsonSerializer.Deserialize<CheckProducer>(snapshot.Files[RepoPath.CreateKnown(path)].Text, JsonOptions);
            if (producer is null || producer.Schema != "report-producer-scope-v1" || producer.Scripts is null || producer.Projects is null || producer.Materials is null) throw new InvalidDataException("invalid producer registration: " + path);
            var inputs = producer.Scripts.Concat(producer.Projects).Concat(producer.Materials).ToArray();
            EngineeringProjectRegistry.ValidateInputPaths(inputs, path);
            foreach (var input in inputs)
                if (!snapshot.TryGetFile(input, out _)) throw new InvalidDataException($"producer {path} references absent input: {input}");
            return producer;
        }
        catch (JsonException exception) { throw new InvalidDataException($"invalid producer {path}: {exception.Message}", exception); }
    }
}
