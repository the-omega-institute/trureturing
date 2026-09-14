using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanReportCompatibilityDeltaTests
{
    [Theory]
    [InlineData("implementation", "delta")]
    [InlineData("version", "fallback")]
    [InlineData("config", "fallback")]
    public void CanonicalTupleControlsBaselineCompatibilityAndSourceClosure(string change, string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        LeanReportInputScriptTests.InstallReportConfiguration(root);
        Write("lean-toolchain", "leanprover/lean4:fixture\n");
        Write("lakefile.toml", "name = \"fixture\"\n");
        Write("lake-manifest.json", "{}\n");
        Write("Trureturing.lean", "import D5.B\n");
        Write("D5/A.lean", "-- claim\n");
        Write("D5/B.lean", "import D5.A\n");
        Write("D5/C.lean", "-- refutation, no import\n");
        Write("D5/E.lean", "import D5.C\n");
        Write("D5/Removed.lean", "-- removed dependency\n");
        Write("D5/Dependent.lean", "import D5.Removed\n");
        Write("D5/Unrelated.lean", "-- unrelated\n");
        var fields = Address();
        var modules = new JsonArray();
        foreach (var (module, imports) in new (string, string[])[]
                 {
                     ("Trureturing", ["D5.B"]), ("D5.A", []), ("D5.B", ["D5.A"]),
                     ("D5.C", []), ("D5.E", ["D5.C"]), ("D5.Removed", []),
                     ("D5.Dependent", ["D5.Removed"]), ("D5.Unrelated", []),
                 })
        {
            var path = module.Replace('.', '/') + ".lean";
            modules.Add(new JsonObject
            {
                ["module"] = module, ["source_path"] = path,
                ["source_sha256"] = "sha256:" + Hash(File.ReadAllBytes(Path.Combine(root, path))),
                ["imports"] = JsonSerializer.SerializeToNode(imports), ["declarations"] = new JsonArray(),
            });
        }
        modules[3]!["utility_refutation"] = new JsonObject
        {
            ["claim_source_path"] = "D5/A.lean", ["claim_source_sha256"] = modules[1]!["source_sha256"]!.DeepClone(),
        };
        var oldAddress = CacheAddress(fields);
        var cache = Path.Combine(root, "cache");
        var report = $"cache/{oldAddress}/raw-lean-report.json";
        Write(report, new JsonObject { ["modules"] = modules, ["schema"] = "stratalint-raw-lean-report-v2" }.ToJsonString());
        var reportHash = Hash(File.ReadAllBytes(Path.Combine(root, report)));
        Write(report + ".sha256", $"{reportHash}  raw-lean-report.json\n");
        using (ZipFile.Open(Path.Combine(root, report + ".materials.zip"), ZipArchiveMode.Create)) { }
        Write(report + ".input.attestation", "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={fields[0]}\nproducer_sha256={fields[1]}\nreport_sha256={reportHash}\n");
        Write(report + ".provenance.json", JsonSerializer.Serialize(new
        {
            schema = "stratalint-lean-report-provenance-v1", side = "candidate", mode = "produced", source_side = "candidate",
            input_address = "sha256:" + oldAddress, producer_sha256 = fields[1], repository_inspector_sha256 = fields[1],
            lean_sources_sha256 = fields[2], lean_config_sha256 = fields[3], report_sha256 = reportHash,
        }));

        Write("D5/A.lean", "-- changed claim\n");
        Write("D5/Added.lean", "-- added module\n");
        File.Delete(Path.Combine(root, "D5/Removed.lean"));
        if (change == "version") Write(LeanReportInputScriptTests.CompatibilityPath,
            "compatibility_version = 2\n" + LeanReportInputScriptTests.SourcePatterns);
        else if (change == "config") Write("lakefile.toml", "name = \"changed\"\n");
        else
        {
            Write("tools/StrataLint.Engine/Producer.cs", "// changed C#\n");
            Write("tools/scripts/report/lean-report-input.sh", "# changed helper\n");
            Write("tools/lean-inspector/Inspector.lean", "-- changed generator\n");
            Write("tools/lean-inspector/Unused/Fixture.lean", "-- unused fixture\n");
        }
        fields = Address();
        var table = Path.Combine(root, "modules.tsv");
        File.WriteAllBytes(table, Helper("modules").StandardOutput);
        var plan = Path.Combine(root, "plan.json");
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "plan",
                root, cache, CacheAddress(fields), fields[1], fields[1], fields[3], table, plan], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        using var document = JsonDocument.Parse(File.ReadAllBytes(plan));
        Assert.Equal(mode, document.RootElement.GetProperty("status").GetString());
        if (mode == "delta")
        {
            Assert.Equal(new[] { "D5.A" }, Names("changed"));
            Assert.Equal(new[] { "D5.Added" }, Names("added"));
            Assert.Equal(new[] { "D5.Removed" }, Names("removed"));
            Assert.Equal(new[] { "D5.A", "D5.Added", "D5.B", "D5.C", "D5.Dependent", "D5.E", "Trureturing" }, Names("recheck"));
        }

        string[] Names(string key) => document.RootElement.GetProperty(key).EnumerateArray().Select(x => x.GetString()!).ToArray();
        string[] Address() => Encoding.UTF8.GetString(Helper("address").StandardOutput).Trim().Split(' ');
        ProcessOutput Helper(string command)
        {
            var result = TestProcessRunner.Run("env",
                [$"STRATALINT_LEAN_INPUT_MEMO_ROOT={Path.Combine(root, "memo")}", "bash",
                    Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/lean-report-input.sh"),
                    command, "--repository", root], root, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            return result;
        }
        void Write(string relative, string text)
        {
            var path = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text, new UTF8Encoding(false));
        }
    }

    private static string Hash(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static string CacheAddress(string[] fields) => Hash(Encoding.UTF8.GetBytes(
        $"schema=stratalint-lean-report-input-v1\nproducer_sha256={fields[1]}\n"
        + $"repository_inspector_sha256={fields[1]}\nlean_sources_sha256={fields[2]}\nlean_config_sha256={fields[3]}\n"));
}
