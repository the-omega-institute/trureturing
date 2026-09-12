using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportCiBaselineScriptTests
{
    [Fact]
    public void DeltaPlannerRejectsZeroRepositoryAttestation() =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected("repository-zero", false);

    [Fact]
    public void CiBaselineAdapterRejectsZeroRepositoryAttestation() =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected("repository-zero", true);

    [Fact]
    public void DeltaPlannerRejectsMismatchedCacheAddress() =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected("input_address-mismatch", false);

    [Fact]
    public void CiBaselineAdapterRejectsMismatchedCacheAddress() =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected("input_address-mismatch", true);

    [Theory]
    [InlineData("repository-mismatch")]
    [InlineData("repository-missing")]
    [InlineData("repository-malformed")]
    [InlineData("lean_sources_sha256-missing")]
    [InlineData("lean_sources_sha256-malformed")]
    [InlineData("lean_sources_sha256-nonstring")]
    [InlineData("lean_sources_sha256-mismatch")]
    [InlineData("producer_sha256-mismatch")]
    [InlineData("repository_inspector_sha256-mismatch")]
    [InlineData("lean_config_sha256-mismatch")]
    public void DeltaPlannerRejectsIncompleteOrInconsistentIdentity(string damage) =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected(damage, false);

    [Theory]
    [InlineData("repository-mismatch")]
    [InlineData("repository-missing")]
    [InlineData("repository-malformed")]
    [InlineData("lean_sources_sha256-missing")]
    [InlineData("lean_sources_sha256-malformed")]
    [InlineData("lean_sources_sha256-nonstring")]
    [InlineData("lean_sources_sha256-mismatch")]
    [InlineData("producer_sha256-mismatch")]
    [InlineData("repository_inspector_sha256-mismatch")]
    [InlineData("lean_config_sha256-mismatch")]
    public void CiBaselineAdapterRejectsIncompleteOrInconsistentIdentity(string damage) =>
        LeanReportCiBaselineScriptContract.AssertInvalidIdentityRejected(damage, true);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StaleBaselineRechecksChangedModuleAndReverseImportersThroughMerge(bool viaAdapter) =>
        LeanReportCiBaselineScriptContract.AssertStaleBaselineMerge(viaAdapter);

    [Fact]
    public void DeltaBaselineWithDanglingLogsSymlinkIsRejected() =>
        LeanReportCiBaselineScriptContract.AssertDeltaBaselineWithDanglingLogsSymlinkIsRejected();

    [Fact]
    public void CiBaselineAdapterDoesNotCopyProducerLogsIntoDeltaCache() =>
        LeanReportCiBaselineScriptContract.AssertAdapterDoesNotCopyProducerLogsIntoDeltaCache();

    [Fact]
    public void DeltaPlanRechecksTransitiveImportersOfRemovedModule() =>
        LeanReportCiBaselineScriptContract.AssertDeltaPlanRechecksTransitiveImportersOfRemovedModule();

    [Fact]
    public void DeltaPlanDoesNotRecheckModuleOutsideRemovedDependencyClosure() =>
        LeanReportCiBaselineScriptContract.AssertDeltaPlanDoesNotRecheckModuleOutsideRemovedDependencyClosure();

    [Fact]
    public void DeltaPlanRechecksExactlySurvivingDescendantsOfRemovedModules() =>
        LeanReportCiBaselineScriptContract.AssertDeltaPlanRechecksExactlySurvivingDescendantsOfRemovedModules();

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UtilityClaimOutsideImportClosureInvalidatesDependentRefutation(bool removed) =>
        LeanReportCiBaselineScriptContract.AssertUtilityClaimInvalidatesRefutation(removed);
}

internal static class LeanReportCiBaselineScriptContract
{
    private const string ScriptPath = "tools/scripts/report/lean-report-ci-baseline.sh";
    private const string Producer = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    private const string Resident = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
    private const string Sources = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    private const string Config = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    private static string RepositoryFields => $"repository_inspector_sha256={Resident}\nlean_sources_sha256={Sources}\nlean_config_sha256={Config}\n";
    private static string RepositoryAddress => Hash("schema=stratalint-lean-report-repository-input-v1\n" + RepositoryFields);
    private static string Address => Hash($"schema=stratalint-lean-report-input-v1\nproducer_sha256={Producer}\n" + RepositoryFields);

    internal static void AssertInvalidIdentityRejected(string damage, bool viaAdapter)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        var a = CreateModuleRecord(temporary.Path, "D5.A");
        // Reproduce the bad seed: B's source imports A, but the stored edge is absent.
        var b = JsonNode.Parse(CreateModuleRecord(temporary.Path, "D5.B", "D5.A"))!;
        b["imports"] = new JsonArray();
        WriteBundle(bundle, string.Join(", ", a, b.ToJsonString()));
        File.AppendAllText(Path.Combine(temporary.Path, "D5/A.lean"), "-- changed\n");
        var provenance = JsonNode.Parse(File.ReadAllText(bundle + ".provenance.json"))!.AsObject();
        var attestation = File.ReadAllLines(bundle + ".input.attestation");
        switch (damage)
        {
            case "repository-zero": attestation[1] = "repository_input_sha256=" + new string('0', 64); break;
            case "repository-mismatch": attestation[1] = "repository_input_sha256=" + Address; break;
            case "repository-missing": attestation = [attestation[0], attestation[2], attestation[3]]; break;
            case "repository-malformed": attestation[1] = "repository_input_sha256=invalid"; break;
            default:
                var parts = damage.Split('-');
                var field = parts[0];
                if (parts[1] == "missing") provenance.Remove(field);
                else if (parts[1] == "nonstring") provenance[field] = 42;
                else provenance[field] = parts[1] == "malformed" ? "invalid"
                    : (field == "input_address" ? "sha256:" : "") + new string('0', 64);
                if (field == "producer_sha256") attestation[2] = "producer_sha256=" + provenance[field]!.GetValue<string>();
                break;
        }
        File.WriteAllText(bundle + ".provenance.json", provenance.ToJsonString());
        File.WriteAllLines(bundle + ".input.attestation", attestation, new UTF8Encoding(false));

        if (viaAdapter)
        {
            var result = Run(bundle, cache);
            Assert.Equal(0, result.ExitCode);
            Assert.Empty(result.StandardOutput);
            Assert.Contains("status=fallback reason=invalid-attestation", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
            Assert.False(Directory.Exists(cache));
        }
        else
        {
            StageBundle(bundle, cache, provenance["input_address"]!.GetValue<string>()[7..]);
            using var plan = JsonDocument.Parse(File.ReadAllText(RunDeltaPlan(temporary.Path, cache,
                "D5.A\tD5/A.lean\nD5.B\tD5/B.lean\n")));
            Assert.Equal("fallback", plan.RootElement.GetProperty("status").GetString());
            Assert.False(plan.RootElement.TryGetProperty("baseline", out _));
        }
    }

    internal static void AssertStaleBaselineMerge(bool viaAdapter)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        var modules = new[]
        {
            CreateModuleRecord(temporary.Path, "D5.A"),
            CreateModuleRecord(temporary.Path, "D5.B", "D5.A"),
            CreateModuleRecord(temporary.Path, "D5.C", "D5.B"),
            CreateModuleRecord(temporary.Path, "D5.Unrelated"),
        };
        WriteBundle(bundle, string.Join(", ", modules));
        if (viaAdapter)
        {
            var result = Run(bundle, cache);
            Assert.Equal(0, result.ExitCode);
            Assert.Contains("status=ready", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        }
        else StageBundle(bundle, cache, Address);
        var source = Path.Combine(temporary.Path, "D5/A.lean");
        File.AppendAllText(source, "-- changed\n");
        var planPath = RunDeltaPlan(temporary.Path, cache,
            "D5.A\tD5/A.lean\nD5.B\tD5/B.lean\nD5.C\tD5/C.lean\nD5.Unrelated\tD5/Unrelated.lean\n");
        using var plan = JsonDocument.Parse(File.ReadAllText(planPath));
        Assert.Equal("delta", plan.RootElement.GetProperty("status").GetString());
        Assert.Equal(new[] { "D5.A" }, Names("changed"));
        Assert.Equal(new[] { "D5.A", "D5.B", "D5.C" }, Names("recheck"));
        var changed = JsonNode.Parse(modules[0])!;
        changed["source_sha256"] = "sha256:" + Hash(File.ReadAllText(source));
        var subset = Path.Combine(temporary.Path, "subset", "raw-lean-report.json");
        WriteBundle(subset, string.Join(", ", changed.ToJsonString(), modules[1], modules[2]));
        var output = Path.Combine(temporary.Path, "merged.json");
        var merged = TestProcessRunner.Run("python3",
            [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "merge", planPath, subset, output],
            temporary.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(merged.ExitCode == 0, Encoding.UTF8.GetString(merged.StandardError));
        using var report = JsonDocument.Parse(File.ReadAllText(output));
        var records = report.RootElement.GetProperty("modules").EnumerateArray().ToArray();
        Assert.Equal(new[] { "D5.A", "D5.B", "D5.C", "D5.Unrelated" }, records.Select(x => x.GetProperty("module").GetString()));
        Assert.Equal("sha256:" + Hash(File.ReadAllText(source)), records[0].GetProperty("source_sha256").GetString());
        Assert.Equal("D5.A", records[1].GetProperty("imports")[0].GetString());
        Assert.Equal(modules[3], records[3].GetRawText());
        using var materials = ZipFile.OpenRead(output + ".materials.zip");
        Assert.Empty(materials.Entries);

        string?[] Names(string key) => plan.RootElement.GetProperty(key).EnumerateArray().Select(x => x.GetString()).ToArray();
    }

    private static void StageBundle(string bundle, string cache, string address)
    {
        var entry = Path.Combine(cache, address, "raw-lean-report.json");
        Directory.CreateDirectory(Path.GetDirectoryName(entry)!);
        foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip" })
            File.Copy(bundle + suffix, entry + suffix);
    }

    private static string Hash(string text) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text)));

    public static void AssertTrustedStagingAndFailClosedFallbacks()
    {
        if (OperatingSystem.IsWindows()) return;

        CompleteFlatBundleBecomesAContentAddressedDeltaEntry();
        DeltaBaselineWithLegacyLogsIsRejected();
        foreach (var damage in new[] { "missing-provenance", "damaged-provenance", "missing-materials" })
        {
            UntrustedBundleIsANonFatalBaselineMiss(damage);
        }
    }

    private static void DeltaBaselineWithLegacyLogsIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);
        Assert.Equal(0, Run(bundle, cache).ExitCode);
        var entry = Path.Combine(cache, Address, "raw-lean-report.json");
        Directory.CreateDirectory(entry + ".logs");
        File.WriteAllText(
            Path.Combine(entry + ".logs", "producer.log"),
            "legacy\n",
            new UTF8Encoding(false));

        var plan = RunDeltaPlan(temporary.Path, cache);

        Assert.Contains("\"status\": \"fallback\"", File.ReadAllText(plan), StringComparison.Ordinal);
    }

    internal static void AssertDeltaBaselineWithDanglingLogsSymlinkIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);
        Assert.Equal(0, Run(bundle, cache).ExitCode);
        var entry = Path.Combine(cache, Address, "raw-lean-report.json");
        File.CreateSymbolicLink(
            entry + ".logs",
            Path.Combine(cache, Address, "missing-producer-logs"));

        var plan = RunDeltaPlan(temporary.Path, cache);

        Assert.Contains("\"status\": \"fallback\"", File.ReadAllText(plan), StringComparison.Ordinal);
    }

    internal static void AssertAdapterDoesNotCopyProducerLogsIntoDeltaCache()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);
        Directory.CreateDirectory(bundle + ".logs");
        File.WriteAllText(
            Path.Combine(bundle + ".logs", "producer.log"),
            "producer diagnostics\n",
            new UTF8Encoding(false));

        var result = Run(bundle, cache);

        Assert.Equal(0, result.ExitCode);
        var entry = Path.Combine(cache, Address, "raw-lean-report.json");
        Assert.False(Directory.Exists(entry + ".logs"));
        Assert.Contains(
            "LEAN_REPORT_CI_BASELINE status=ready",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    internal static void AssertDeltaPlanRechecksTransitiveImportersOfRemovedModule()
    {
        if (OperatingSystem.IsWindows()) return;

        var recheck = RunRemovedDependencyPlan(includeUnrelatedModule: false);

        Assert.Equal(new[] { "B", "C" }, recheck);
    }

    internal static void AssertDeltaPlanDoesNotRecheckModuleOutsideRemovedDependencyClosure()
    {
        if (OperatingSystem.IsWindows()) return;

        var recheck = RunRemovedDependencyPlan(includeUnrelatedModule: true);

        Assert.DoesNotContain("D", recheck);
    }

    internal static void AssertDeltaPlanRechecksExactlySurvivingDescendantsOfRemovedModules()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        // Imports point toward dependencies: B/C survive A, while I survives removed H.
        // E/F/G/J fork and join downstream; S/T are forward-only, D/U disconnected.
        var baselineModules = new[]
        {
            CreateModuleRecord(temporary.Path, "A"),
            CreateModuleRecord(temporary.Path, "B", "A", "S"),
            CreateModuleRecord(temporary.Path, "C", "A"),
            CreateModuleRecord(temporary.Path, "D"),
            CreateModuleRecord(temporary.Path, "E", "B"),
            CreateModuleRecord(temporary.Path, "F", "B", "C"),
            CreateModuleRecord(temporary.Path, "G", "E", "F"),
            CreateModuleRecord(temporary.Path, "H", "A"),
            CreateModuleRecord(temporary.Path, "I", "H"),
            CreateModuleRecord(temporary.Path, "J", "G", "I"),
            CreateModuleRecord(temporary.Path, "S"),
            CreateModuleRecord(temporary.Path, "T", "S"),
            CreateModuleRecord(temporary.Path, "U", "D"),
        };
        var surviving = new[] { "B", "C", "D", "E", "F", "G", "I", "J", "S", "T", "U" };
        var moduleTable = string.Concat(surviving.Select(module => $"{module}\t{module}.lean\n"));
        WriteBundle(bundle, string.Join(", ", baselineModules));
        Assert.Equal(0, Run(bundle, cache).ExitCode);

        var plan = RunDeltaPlan(temporary.Path, cache, moduleTable);
        using var document = JsonDocument.Parse(FixtureFile.ReadAllText(plan));
        var root = document.RootElement;
        Assert.Equal("delta", root.GetProperty("status").GetString());
        Assert.Empty(root.GetProperty("changed").EnumerateArray());
        Assert.Empty(root.GetProperty("added").EnumerateArray());
        Assert.Equal(
            new[] { "A", "H" },
            root.GetProperty("removed").EnumerateArray().Select(value => value.GetString()).ToArray());
        Assert.Equal(surviving, root.GetProperty("current").EnumerateObject().Select(value => value.Name).ToArray());
        Assert.Equal(
            new[] { "B", "C", "E", "F", "G", "I", "J" },
            root.GetProperty("recheck").EnumerateArray().Select(value => value.GetString()).ToArray());
    }

    internal static void AssertUtilityClaimInvalidatesRefutation(bool removed)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        var claim = JsonNode.Parse(CreateModuleRecord(temporary.Path, "A"))!;
        var result = JsonNode.Parse(CreateModuleRecord(temporary.Path, "B"))!;
        result["utility_refutation"] = new JsonObject
        {
            ["claim_gid"] = "D5/S0/Carrier/A.claim",
            ["claim_source_path"] = "A.lean",
            ["claim_source_sha256"] = claim["source_sha256"]!.GetValue<string>(),
            ["result_gid"] = "D5/S0/Carrier/B.result",
            ["is_closed_negation"] = true,
        };
        WriteBundle(bundle, string.Join(", ", claim.ToJsonString(), result.ToJsonString(),
            CreateModuleRecord(temporary.Path, "C", "B"), CreateModuleRecord(temporary.Path, "D")));
        Assert.Equal(0, Run(bundle, cache).ExitCode);
        File.WriteAllText(Path.Combine(temporary.Path, "A.lean"), "-- changed claim\n");
        var table = (removed ? "" : "A\tA.lean\n") + "B\tB.lean\nC\tC.lean\nD\tD.lean\n";

        using var document = JsonDocument.Parse(FixtureFile.ReadAllText(RunDeltaPlan(temporary.Path, cache, table)));

        Assert.Equal(removed ? new[] { "B", "C" } : new[] { "A", "B", "C" },
            document.RootElement.GetProperty("recheck").EnumerateArray().Select(item => item.GetString()).ToArray());
    }

    private static void CompleteFlatBundleBecomesAContentAddressedDeltaEntry()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);

        var result = Run(bundle, cache);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(cache, Encoding.UTF8.GetString(result.StandardOutput).Trim());
        var entry = Path.Combine(cache, Address, "raw-lean-report.json");
        foreach (var suffix in new[]
                 {
                     "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip",
                 })
        {
            Assert.True(File.Exists(entry + suffix), $"staged baseline member is missing: {suffix}");
        }
        Assert.False(Directory.Exists(entry + ".logs"));
        var plan = RunDeltaPlan(temporary.Path, cache);
        Assert.Contains("\"status\": \"reuse\"", File.ReadAllText(plan), StringComparison.Ordinal);
    }

    private static string RunDeltaPlan(string temporaryPath, string cache, string moduleTable = "")
    {
        var modules = Path.Combine(temporaryPath, "modules.tsv");
        var plan = Path.Combine(temporaryPath, "plan.json");
        File.WriteAllText(modules, moduleTable, new UTF8Encoding(false));
        var delta = TestProcessRunner.Run(
            "python3",
            [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "plan",
                temporaryPath, cache, new string('b', 64), Producer, Resident, Config, modules, plan],
            temporaryPath, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, delta.ExitCode);
        return plan;
    }

    private static string[] RunRemovedDependencyPlan(bool includeUnrelatedModule)
    {
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        var baselineModules = new List<string>
        {
            CreateModuleRecord(temporary.Path, "A"),
            CreateModuleRecord(temporary.Path, "B", "A"),
            CreateModuleRecord(temporary.Path, "C", "B"),
        };
        var moduleTable = "B\tB.lean\nC\tC.lean\n";
        if (includeUnrelatedModule)
        {
            baselineModules.Add(CreateModuleRecord(temporary.Path, "D"));
            moduleTable += "D\tD.lean\n";
        }
        WriteBundle(bundle, string.Join(", ", baselineModules));
        Assert.Equal(0, Run(bundle, cache).ExitCode);

        var plan = RunDeltaPlan(temporary.Path, cache, moduleTable);
        using var document = JsonDocument.Parse(FixtureFile.ReadAllText(plan));
        var root = document.RootElement;
        Assert.Equal("delta", root.GetProperty("status").GetString());
        Assert.Equal(
            new[] { "A" },
            root.GetProperty("removed").EnumerateArray().Select(value => value.GetString()).ToArray());
        if (includeUnrelatedModule)
        {
            Assert.True(root.GetProperty("current").TryGetProperty("D", out _));
        }
        return root.GetProperty("recheck")
            .EnumerateArray()
            .Select(value => value.GetString()!)
            .ToArray();
    }

    private static string CreateModuleRecord(string repository, string module, params string[] imports)
    {
        var relativePath = module.Replace('.', '/') + ".lean";
        var sourcePath = Path.Combine(repository, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(sourcePath)!);
        File.WriteAllText(sourcePath, string.Concat(imports.Select(import => $"import {import}\n")) + $"-- {module}\n", new UTF8Encoding(false));
        var sourceSha = Convert.ToHexString(SHA256.HashData(FixtureFile.ReadAllBytes(sourcePath))).ToLowerInvariant();
        return JsonSerializer.Serialize(new
        {
            module,
            source_path = relativePath,
            source_sha256 = "sha256:" + sourceSha,
            imports,
            declarations = Array.Empty<object>(),
        });
    }

    private static void UntrustedBundleIsANonFatalBaselineMiss(string damage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);
        switch (damage)
        {
            case "missing-provenance":
                File.Delete(bundle + ".provenance.json");
                break;
            case "damaged-provenance":
                File.WriteAllText(bundle + ".provenance.json", "not-json\n", new UTF8Encoding(false));
                break;
            case "missing-materials":
                File.Delete(bundle + ".materials.zip");
                break;
        }

        var result = Run(bundle, cache);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Contains(
            "LEAN_REPORT_CI_BASELINE status=fallback",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(cache, Address)));
    }

    private static ProcessOutput Run(string bundle, string cache)
    {
        var root = TestRepositoryLayout.FindRoot();
        return TestProcessRunner.Run(
            Path.Combine(root, ScriptPath),
            ["--bundle", bundle, "--cache-root", cache],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
    }

    private static void WriteBundle(string report, string moduleRecords = "")
    {
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        File.WriteAllText(
            report,
            $"{{\"modules\": [{moduleRecords}], \"schema\": \"stratalint-raw-lean-report-v2\"}}\n",
            new UTF8Encoding(false));
        var reportSha = Convert.ToHexString(SHA256.HashData(FixtureFile.ReadAllBytes(report))).ToLowerInvariant();
        File.WriteAllText(report + ".sha256", $"{reportSha}  raw-lean-report.json\n", new UTF8Encoding(false));
        File.WriteAllText(
            report + ".input.attestation",
            $"schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256={RepositoryAddress}\nproducer_sha256={Producer}\nreport_sha256={reportSha}\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            report + ".provenance.json",
            $"{{\"schema\":\"stratalint-lean-report-provenance-v1\",\"side\":\"candidate\",\"mode\":\"produced\",\"source_side\":\"candidate\",\"input_address\":\"sha256:{Address}\",\"producer_sha256\":\"{Producer}\",\"repository_inspector_sha256\":\"{Resident}\",\"lean_sources_sha256\":\"{Sources}\",\"lean_config_sha256\":\"{Config}\",\"report_sha256\":\"{reportSha}\"}}\n",
            new UTF8Encoding(false));
        using var materials = ZipFile.Open(report + ".materials.zip", ZipArchiveMode.Create);
    }
}
