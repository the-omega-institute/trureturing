using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.TestSupport;

internal static class ProducerInputFixture
{
    private const string ProjectRegistrationPath = "Meta/engineering-projects.json";
    private const string LeanRegistrationPath = "Meta/ReportProducers/lean-report.json";
    private const string ScribeRegistrationPath = "Meta/ReportProducers/scribe-content.json";
    private const string CliProjectPath = "tools/StrataLint.Cli/StrataLint.Cli.csproj";
    private static readonly Lazy<IReadOnlyDictionary<string, byte[]>> BatchProducerInputs = new(ReadBatchProducerInputs);

    private static IReadOnlyDictionary<string, byte[]> ReadBatchProducerInputs()
    {
        var source = TestRepositoryLayout.FindRoot();
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(source, ProjectRegistrationPath)))!.AsObject();
        var rows = manifest["projects"]!.AsArray();
        var scopes = new[] { LeanRegistrationPath, ScribeRegistrationPath }.ToDictionary(path => path,
            path => JsonNode.Parse(File.ReadAllText(Path.Combine(source, path)))!.AsObject(), StringComparer.Ordinal);
        var selections = scopes.Values.Select(scope =>
        {
            var path = scope["registration"]!.GetValue<string>();
            var inputs = JsonNode.Parse(File.ReadAllText(Path.Combine(source, path)))!;
            return (Path: path, Value: inputs["producer_scopes"]![scope["scope"]!.GetValue<string>()]!);
        }).ToArray();
        // Restrict Git's output to declared inputs before the bounded reader sees it.
        var inventoryPatterns = rows.Select(row => row!["path"]!.GetValue<string>())
            .Concat(rows.SelectMany(row => row!["include"]!.AsArray().Concat(row["exclude"]!.AsArray()))
                .Select(path => path!.GetValue<string>()))
            .Concat(selections.SelectMany(selection => selection.Value["include"]!.AsArray())
                .Select(item => item!["pattern"]!.GetValue<string>()))
            .Concat(manifest["rule_build_inputs"]!.AsArray().Select(path => path!.GetValue<string>()))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).Select(pattern => ":(glob)" + pattern).ToArray();
        var inventory = TestProcessRunner.Run("git", ["ls-files", "--cached", "-z", "--", .. inventoryPatterns], source,
            TestBudgets.ScriptProcessHangGuard, 4 * 1024 * 1024);
        Assert.True(inventory.ExitCode == 0, Encoding.UTF8.GetString(inventory.StandardError));
        // Expand registered tool source globs only. BatchWorld supplies its own Blueprint
        // definitions and Lean/content payloads for the injected documents assembly.
        var available = Encoding.UTF8.GetString(inventory.StandardOutput).Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Where(path => File.Exists(Path.Combine(source, path))).ToArray();
        var registry = EngineeringProjectRegistry.Read(available.Select(path => new EngineeringSource(path, string.Empty))
            .Prepend(new EngineeringSource(ProjectRegistrationPath, manifest.ToJsonString())).ToArray());
        var roots = scopes.Values.SelectMany(scope => scope["projects"]!.AsArray())
            .Select(path => path!.GetValue<string>()).Append(CliProjectPath);
        var paths = registry.ProjectInputs(roots, available.Where(path => path.StartsWith("tools/", StringComparison.Ordinal)).ToArray(), []).ToHashSet(StringComparer.Ordinal);
        manifest["projects"] = new JsonArray(rows.Where(row => paths.Contains(row!["path"]!.GetValue<string>()))
            .Select(row => row!.DeepClone()).ToArray());
        manifest["historical_projects"] = new JsonArray();
        paths.UnionWith(manifest["rule_build_inputs"]!.AsArray().Select(path => path!.GetValue<string>()));
        paths.UnionWith(scopes.Keys);
        foreach (var (inputPath, selection) in selections)
        {
            paths.Add(inputPath);
            var includes = selection["include"]!.AsArray()
                .Select(item => (Pattern: item!["pattern"]!.GetValue<string>(), Optional: item["optional"]!.GetValue<bool>()))
                .Where(item => !item.Optional || item.Pattern.Contains('*') || available.Contains(item.Pattern, StringComparer.Ordinal))
                .Select(item => item.Pattern).ToArray();
            var excludes = selection["exclude"]!.AsArray().Select(item => item!.GetValue<string>()).Append("Blueprint/**").ToArray();
            paths.UnionWith(EngineeringProjectRegistry.ExpandInputs(available, includes, excludes, inputPath));
        }
        paths.UnionWith(["lean-toolchain", "lakefile.toml", "lake-manifest.json", ".gitignore"]);
        var files = paths.ToDictionary(path => path, path => File.ReadAllBytes(Path.Combine(source, path)), StringComparer.Ordinal);
        // Match this synthetic report's local/core-only rows. Keep the actual
        // native registration; the producer below captures this workspace and
        // its separate package namespace with the production implementation.
        files["lakefile.toml"] = Encoding.UTF8.GetBytes("""
            name = "batchFixture"
            defaultTargets = ["Batch"]
            [[lean_lib]]
            name = "Batch"
            roots = ["D5", "Trureturing"]
            [[require]]
            name = "batchSupport"
            path = ".lake/packages/batchSupport"
            """);
        files["lake-manifest.json"] = Encoding.UTF8.GetBytes("""
            {"version":"1.2.0","name":"batchFixture","lakeDir":".lake","packagesDir":".lake/packages","packages":[
              {"name":"batchSupport","type":"path","scope":"","dir":".lake/packages/batchSupport","configFile":"lakefile.toml","manifestFile":"lake-manifest.json","inherited":false}]}
            """);
        files.Add(ProjectRegistrationPath, Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        return files;
    }

    internal static IReadOnlyCollection<string> CopyBatchProducerInputs(string root)
    {
        var files = BatchProducerInputs.Value;
        var source = TestRepositoryLayout.FindRoot();
        var registrationPath = Path.Combine(root, ProjectRegistrationPath);
        var existing = JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(registrationPath))!.AsObject();
        var added = JsonNode.Parse(files[ProjectRegistrationPath])!.AsObject();
        foreach (var row in added["projects"]!.AsArray())
        {
            Assert.DoesNotContain(existing["projects"]!.AsArray(),
                prior => prior!["path"]!.GetValue<string>() == row!["path"]!.GetValue<string>());
            existing["projects"]!.AsArray().Add(row!.DeepClone());
        }
        existing["rule_build_inputs"] = new JsonArray(existing["rule_build_inputs"]!.AsArray()
            .Concat(added["rule_build_inputs"]!.AsArray()).Select(path => path!.GetValue<string>())
            .Distinct(StringComparer.Ordinal).Select(path => JsonValue.Create(path)).ToArray());
        foreach (var (relative, bytes) in files.Where(pair => pair.Key != ProjectRegistrationPath))
        {
            var destination = Path.Combine(root, relative);
            Assert.False(TemporaryFileSystem.File.Exists(destination), "producer input already supplied: " + relative);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllBytes(destination, bytes);
            if (!OperatingSystem.IsWindows())
                File.SetUnixFileMode(destination, File.GetUnixFileMode(Path.Combine(source, relative)));
        }
        TemporaryFileSystem.File.WriteAllText(registrationPath, existing.ToJsonString());
        return files.Keys.ToArray();
    }

    internal static void AttestBatchReport(string root, string report)
    {
        // Only fixture data are synthesized here. Hashes, modes, source
        // population, coordinates and sidecars come from their existing owners.
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, sys
            from pathlib import Path
            root, report = map(Path, sys.argv[1:])
            sys.path.insert(0, str(root / 'tools/lean-inspector'))
            import native, publication, materials
            support = root / '.lake/packages/batchSupport'
            support.mkdir(parents=True, exist_ok=True)
            (support / 'lakefile.toml').write_text('name = "batchSupport"\n[[lean_lib]]\nname = "BatchSupport"\n')
            (support / 'BatchSupport.lean').write_text('def batchSupport : Nat := 1\n')
            rows = publication.read_json(report.read_bytes())['modules']
            pin = json.loads((root / 'lake-manifest.json').read_text())['packages'][0]
            configs = ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']
            descriptor = dict(kind='lake-fetched', complete_defaults=True, packages_dir='.lake/packages',
                workspace_overrides='.lake/package-overrides.json', excluded_dirs=['.lake'], packages=[
                dict(owner='batchFixture', dir='.', source_roots=['D5', 'Trureturing.lean'],
                     config_paths=configs, remote_url='', scope='', pin=None,
                     modules=[dict(name=row['module'], path=row['source_path']) for row in rows]),
                dict(owner='batchSupport', dir='.lake/packages/batchSupport',
                     source_roots=['.lake/packages/batchSupport/BatchSupport.lean'],
                     config_paths=configs, remote_url='', scope='', pin=pin,
                     modules=[dict(name='BatchSupport', path='BatchSupport.lean')])])
            population = native.native_population(root, descriptor)
            native.write_if_changed(native.state(root) / 'lake-inputs.json', materials.canonical_json(
                dict(descriptor=descriptor, resolver=population['resolver'])))
            inputs = publication.coordinates(root)
            origins = {}
            for row in rows:
                origins[row['module']] = dict(module=row['module'],
                    report_sha256=publication.hashlib.sha256(materials.canonical_json(
                        dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest(),
                    compatibility_sha256=inputs['producer'], producer_sources_sha256='1' * 64,
                    inspector_executable_sha256='2' * 64,
                    input_sources={row['source_path']: row['source_sha256'][7:]}, external_inputs=[])
            publication.write_sidecars(report, inputs, origins, native_inputs=population)
            publication.verify_inputs(report, root)
            """, root, report], root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

}
