using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.EngineeringScope;
using Xunit;
using static StrataLint.TestSupport.ExecutionFixture;

namespace StrataLint.TestSupport;

internal static class NativeReleaseFixture
{
    internal static string NativeRunner => Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
    internal static (int Exit, string Text) Native(string root, string[] args, string? processors = null) =>
        EngineeringProcess.Process(root, NativeRunner, args, processors is null ? null : new Dictionary<string, string> { ["DOTNET_PROCESSOR_COUNT"] = processors });
    internal static JsonNode Read(string root, string path) => JsonNode.Parse(File.ReadAllText(Path.Combine(root, path)))!;
    internal static void Rebind(string root, string record, params string[] paths)
    {
        var data = Read(root, record);
        foreach (var item in data["materials"]!.AsArray().Where(m => paths.Contains(m!["path"]!.ToString())))
            item!["sha256"] = CommonExecutionEvidence.Hash(Path.Combine(root, item["path"]!.ToString()));
        File.WriteAllText(Path.Combine(root, record), data.ToJsonString());
    }
    internal static void Produce(ResourceFixture fixture)
    {
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
    }
    internal static string Pack(ResourceFixture fixture, int run)
    {
        var tar = Path.Combine(fixture.Root, "build/ci-current.tar.gz");
        using var output = new StringWriter();
        var exit = Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "current", "--commit", fixture.Commit,
            "--run-id", run.ToString(System.Globalization.CultureInfo.InvariantCulture), "--run-attempt", "1", "--archive", tar], TestResultEvidence.Load, output, output);
        Assert.True(exit == 0, output.ToString());
        var archive = Path.Combine(fixture.Root, "build/artifact.zip");
        using (var zip = ZipFile.Open(archive, ZipArchiveMode.Create)) zip.CreateEntryFromFile(tar, "ci-current.tar.gz");
        return archive;
    }
    internal static void Capture(string root, string name, (int Exit, string Text) result)
    {
        if (Environment.GetEnvironmentVariable("SOURCE_CONTRACT_EVIDENCE") is not { Length: > 0 } destination) return;
        var target = Path.Combine(destination, name);
        Directory.CreateDirectory(target);
        File.WriteAllText(Path.Combine(target, "process.json"), JsonSerializer.Serialize(new { root, result.Exit, result.Text, native_runner = NativeRunner,
            native_dll_sha256 = CommonExecutionEvidence.Hash(typeof(Program).Assembly.Location) }));
        foreach (var path in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.CurrentPath, CommonExecutionEvidence.ChecksPath("current"),
            CiTransport.ManifestPath("current"), "build/ci/plan.json", "build/ci/changes.json", "build/ci/engineering-result.json", "build/ci/current-result.json",
            "build/cold-events", "build/launched" })
            if (File.Exists(Path.Combine(root, path))) File.Copy(Path.Combine(root, path), Path.Combine(target, Path.GetFileName(path)), true);
        foreach (var record in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.CurrentPath })
        {
            if (!File.Exists(Path.Combine(root, record))) continue;
            foreach (var material in Read(root, record)["materials"]!.AsArray())
            {
                var path = material!["path"]!.ToString();
                if (!File.Exists(Path.Combine(root, path))) continue;
                var copy = Path.Combine(target, "materials", path);
                Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
                File.Copy(Path.Combine(root, path), copy, true);
            }
        }
        if (File.Exists(Path.Combine(root, "build/artifact.zip")))
            File.Copy(Path.Combine(root, "build/artifact.zip"), Path.Combine(target, "original-artifact.zip"), true);
        foreach (var line in result.Text.Split('\n').Where(s => s.StartsWith("PREFLIGHT_ARTIFACT bundle=", StringComparison.Ordinal)))
            File.Copy(line["PREFLIGHT_ARTIFACT bundle=".Length..], Path.Combine(target, "preflight-candidate.tar.gz"), true);
    }
}
