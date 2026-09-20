using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.TestSupport;

internal static class ProducerInputFixture
{
    private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
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
        var selections = scopes.Values.SelectMany(scope =>
        {
            var path = scope["registration"]!.GetValue<string>();
            var inputs = JsonNode.Parse(File.ReadAllText(Path.Combine(source, path)))!;
            var producer = inputs["producer_scopes"]![scope["scope"]!.GetValue<string>()]!;
            return new[] { producer, inputs["inspector_sources"], inputs["dependency_sources"], inputs["config_inputs"] }
                .OfType<JsonNode>().Select(selection => (Path: path, Value: selection));
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
        files.Add(ProjectRegistrationPath, Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        return files;
    }

    internal static IReadOnlyCollection<string> CopyBatchProducerInputs(string root)
    {
        var files = BatchProducerInputs.Value;
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
        }
        TemporaryFileSystem.File.WriteAllText(registrationPath, existing.ToJsonString());
        return files.Keys.ToArray();
    }

    internal static void AttestBatchReport(string root, string report)
    {
        var result = TestProcessRunner.Run("/bin/bash",
            [Path.Combine(root, InputHelperPath), "address", "--repository", root], root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var fields = Encoding.UTF8.GetString(result.StandardOutput).Trim().Split(' ');
        var hash = Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report)));
        TemporaryFileSystem.File.WriteAllText(report + ".sha256", $"{hash}  {Path.GetFileName(report)}\n");
        WriteFixtureOrigins(report, fields[1]);
        TemporaryFileSystem.File.WriteAllText(report + ".input.attestation",
            "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={fields[0]}\nproducer_sha256={fields[1]}\nreport_sha256={hash}\n");
    }

    private static void WriteFixtureOrigins(string report, string compatibility)
    {
        using var document = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllBytes(report));
        var origins = document.RootElement.GetProperty("modules").EnumerateArray().ToDictionary(
            row => row.GetProperty("module").GetString()!, row => new
            {
                module = row.GetProperty("module").GetString(),
                report_sha256 = Convert.ToHexStringLower(SHA256.HashData(StructuredCanonicalWriter.WriteJson(
                    JsonSerializer.SerializeToElement(new { schema = "stratalint-raw-lean-report-v2", modules = new[] { row } })).AsSpan())),
                compatibility_sha256 = compatibility,
                producer_sources_sha256 = new string('1', 64),
                inspector_executable_sha256 = new string('2', 64),
            }, StringComparer.Ordinal);
        TemporaryFileSystem.File.WriteAllText(report + ".provenance.json", JsonSerializer.Serialize(new { module_origins = origins }));
    }

}
