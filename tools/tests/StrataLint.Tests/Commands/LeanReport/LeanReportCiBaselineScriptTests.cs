using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class LeanReportCiBaselineScriptContract
{
    private const string ScriptPath = "tools/scripts/report/lean-report-ci-baseline.sh";
    private const string Address = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string Producer = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    private const string Resident = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
    private const string Config = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

    public static void AssertTrustedStagingAndFailClosedFallbacks()
    {
        if (OperatingSystem.IsWindows()) return;

        CompleteFlatBundleBecomesAContentAddressedDeltaEntry();
        foreach (var damage in new[] { "missing-provenance", "damaged-provenance", "missing-materials" })
        {
            UntrustedBundleIsANonFatalBaselineMiss(damage);
        }
    }

    private static void CompleteFlatBundleBecomesAContentAddressedDeltaEntry()
    {
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
        var modules = Path.Combine(temporary.Path, "modules.tsv");
        var plan = Path.Combine(temporary.Path, "plan.json");
        File.WriteAllText(modules, string.Empty, new UTF8Encoding(false));
        var delta = BoundedProcessRunner.Run(
            "python3",
            [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "plan",
                temporary.Path, cache, new string('b', 64), Producer, Resident, Config, modules, plan],
            temporary.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, delta.ExitCode);
        Assert.Contains("\"status\": \"reuse\"", File.ReadAllText(plan), StringComparison.Ordinal);
    }

    private static void UntrustedBundleIsANonFatalBaselineMiss(string damage)
    {
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
        return BoundedProcessRunner.Run(
            Path.Combine(root, ScriptPath),
            ["--bundle", bundle, "--cache-root", cache],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
    }

    private static void WriteBundle(string report)
    {
        const string sources = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
        const string repository = "1111111111111111111111111111111111111111111111111111111111111111";
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n", new UTF8Encoding(false));
        var reportSha = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(report))).ToLowerInvariant();
        File.WriteAllText(report + ".sha256", $"{reportSha}  raw-lean-report.json\n", new UTF8Encoding(false));
        File.WriteAllText(
            report + ".input.attestation",
            $"schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256={repository}\nproducer_sha256={Producer}\nreport_sha256={reportSha}\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            report + ".provenance.json",
            $"{{\"schema\":\"stratalint-lean-report-provenance-v1\",\"side\":\"candidate\",\"mode\":\"produced\",\"source_side\":\"candidate\",\"input_address\":\"sha256:{Address}\",\"producer_sha256\":\"{Producer}\",\"repository_inspector_sha256\":\"{Resident}\",\"lean_sources_sha256\":\"{sources}\",\"lean_config_sha256\":\"{Config}\",\"report_sha256\":\"{reportSha}\"}}\n",
            new UTF8Encoding(false));
        File.WriteAllText(report + ".materials.zip", "materials\n", new UTF8Encoding(false));
    }
}
