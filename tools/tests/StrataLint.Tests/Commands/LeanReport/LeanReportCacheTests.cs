using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportCacheTests
{
    [Theory]
    [InlineData("test_exact_hit_always_enters_producer_and_rebinds_candidate")]
    [InlineData("test_real_producer_failure_cannot_be_masked_by_prior_report")]
    [InlineData("test_corrupt_seed_and_failed_save_do_not_override_production")]
    [InlineData("test_invalid_producer_outputs_never_replace_prior_bundle")]
    public void IncrementalSeedBehavior(string behavior) => LeanSeedProcessContract.Run("PairTests." + behavior);

    [Theory]
    [InlineData("unchanged")]
    [InlineData("claim")]
    [InlineData("claim-dependency")]
    [InlineData("deleted-claim")]
    [InlineData("result")]
    public void RefutationSeedsRetainMaterialsAndInvalidateClaimDependents(string change)
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var producer = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector");
        const string partition = "0123456789abcdef0123456789abcdef01234567/linux-x64";
        var identity = new string('a', 64);
        var cache = Path.Combine(root, "cache", partition);
        var baseline = Path.Combine(cache, identity, "raw-lean-report.json");
        string[] names = ["Claim", "ClaimDependency", "Consumer", "Result", "Unrelated"];
        foreach (var name in names) Write(name + ".lean", "def value := 1\n");
        Compact(baseline, names);
        var reportHash = Hash(File.ReadAllBytes(baseline));
        Write(baseline + ".sha256", reportHash + "  raw-lean-report.json\n");
        Write(baseline + ".input.attestation", "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={identity}\nproducer_sha256={identity}\nreport_sha256={reportHash}\n");
        Write(baseline + ".provenance.json", JsonSerializer.Serialize(new
        {
            schema = "stratalint-lean-report-provenance-v1", side = "candidate", source_side = "candidate",
            mode = "produced", input_address = "sha256:" + identity, producer_sha256 = identity,
            repository_inspector_sha256 = identity, lean_sources_sha256 = identity,
            lean_config_sha256 = identity, report_sha256 = reportHash,
        }));
        Write(baseline + ".seed.json", JsonSerializer.Serialize(new
        {
            schema = "lean-report-seed-v1", partition, runtime_sha256 = identity, report_sha256 = reportHash,
            materials_sha256 = Hash(FixtureFile.ReadAllBytes(baseline + ".materials.zip")),
        }));
        var changedName = change switch
        {
            "claim" => "Claim", "claim-dependency" => "ClaimDependency", "result" => "Result", _ => null,
        };
        if (changedName is not null) Write(changedName + ".lean", "def value := 2\n");
        if (change == "deleted-claim") File.Delete(Path.Combine(root, "Claim.lean"));
        var current = names.Where(name => File.Exists(Path.Combine(root, name + ".lean"))).ToArray();
        Write("modules.tsv", string.Concat(current.Select(name => name + "\t" + name + ".lean\n")));
        var plan = Path.Combine(root, "plan.json");
        Run("delta.py", "plan", root, cache, identity, identity, identity, identity,
            Path.Combine(root, "modules.tsv"), plan, "--runtime-sha", identity, "--partition", partition);
        using var planned = JsonDocument.Parse(File.ReadAllText(plan));
        Assert.Equal(change == "unchanged" ? "reuse" : "delta", planned.RootElement.GetProperty("status").GetString());
        Assert.False(planned.RootElement.GetProperty("semantic_changed").GetBoolean());
        string[] expected = change switch
        {
            "unchanged" => [], "claim" => ["Claim", "Consumer", "Result"],
            "claim-dependency" => ["Claim", "ClaimDependency", "Consumer", "Result"],
            _ => ["Consumer", "Result"],
        };
        var recheck = planned.RootElement.GetProperty("recheck").EnumerateArray().Select(item => item.GetString()!).ToArray();
        Assert.Equal(expected, recheck);
        if (change == "deleted-claim")
        {
            Assert.Equal("Claim", Assert.Single(planned.RootElement.GetProperty("removed").EnumerateArray()).GetString());
            return;
        }
        var subset = Path.Combine(root, "subset.json");
        Compact(subset, recheck);
        var merged = Path.Combine(root, "merged.json");
        Run("delta.py", "merge", plan, subset, merged);
        var clean = Path.Combine(root, "clean.json");
        Compact(clean, current);
        Assert.Equal(File.ReadAllBytes(clean), File.ReadAllBytes(merged));
        Assert.Equal(FixtureFile.ReadAllBytes(clean + ".materials.zip"), FixtureFile.ReadAllBytes(merged + ".materials.zip"));
        using var mergedReport = JsonDocument.Parse(File.ReadAllText(merged));
        var result = mergedReport.RootElement.GetProperty("modules").EnumerateArray()
            .Single(module => module.GetProperty("module").GetString() == "Result");
        Assert.True(result.GetProperty("utility_refutation").GetProperty("is_closed_negation").GetBoolean());

        void Compact(string output, string[] selected)
        {
            Directory.CreateDirectory(output + ".spool");
            var modules = new JsonArray();
            for (var index = 0; index < selected.Length; index++)
            {
                var name = selected[index];
                var source = File.ReadAllBytes(Path.Combine(root, name + ".lean"));
                Write(Path.Combine(output + ".spool", index + ".statement"), name + ":" + Encoding.UTF8.GetString(source));
                var module = new JsonObject
                {
                    ["module"] = name, ["source_path"] = name + ".lean", ["source_sha256"] = "sha256:" + Hash(source),
                    ["imports"] = name switch { "Claim" => new JsonArray("ClaimDependency"),
                        "Consumer" => new JsonArray("Result"), _ => new JsonArray() },
                    ["declarations"] = new JsonArray(new JsonObject
                    {
                        ["name"] = "value", ["name_key"] = "ns(n0,5:value)", ["kind"] = "def",
                        ["include_in_statement"] = true, ["axioms"] = new JsonArray(),
                        ["material_file"] = index + ".statement",
                    }),
                };
                if (name == "Result") module["utility_refutation"] = new JsonObject
                {
                    ["claim_gid"] = "D5/Claim.value", ["result_gid"] = "D5/Result.value",
                    ["claim_source_path"] = "Claim.lean",
                    ["claim_source_sha256"] = "sha256:" + Hash(File.ReadAllBytes(Path.Combine(root, "Claim.lean"))),
                    ["is_closed_negation"] = true,
                };
                modules.Add(module);
            }
            Write(output + ".spool.json", new JsonObject
            {
                ["schema"] = "stratalint-lean-inspector-spool-v1", ["modules"] = modules,
            }.ToJsonString());
            Run("materials.py", "compact", output + ".spool.json", output + ".spool", output);
        }

        void Write(string relative, string text)
        {
            var path = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text, new UTF8Encoding(false));
        }

        void Run(string script, params string[] arguments)
        {
            var result = TestProcessRunner.Run("python3", new[] { Path.Combine(producer, script) }.Concat(arguments).ToArray(),
                root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        }

        static string Hash(byte[] value) => Convert.ToHexStringLower(SHA256.HashData(value));
    }
}

internal static class LeanSeedProcessContract
{
    internal static void Run(string behavior, TimeSpan? hangGuard = null)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), behavior],
            root, hangGuard ?? TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
