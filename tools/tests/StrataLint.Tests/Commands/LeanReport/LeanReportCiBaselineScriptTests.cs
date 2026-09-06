using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportCiBaselineScriptTests
{
    [Fact]
    public void LeanReportBundleValidatorAcceptsCanonicalProvenanceBytes() =>
        LeanReportCiBaselineScriptContract.AssertCanonicalProvenanceBytesAreAccepted();

    [Fact]
    public void LeanReportBundleValidatorRejectsReorderedProvenanceKeys() =>
        LeanReportCiBaselineScriptContract.AssertNonCanonicalProvenanceBytesAreRejected("reordered-keys");

    [Fact]
    public void LeanReportBundleValidatorRejectsAlteredProvenanceWhitespace() =>
        LeanReportCiBaselineScriptContract.AssertNonCanonicalProvenanceBytesAreRejected("whitespace");

    [Fact]
    public void LeanReportBundleValidatorRejectsDuplicateProvenanceKeys() =>
        LeanReportCiBaselineScriptContract.AssertNonCanonicalProvenanceBytesAreRejected("duplicate-key");

    [Fact]
    public void DeltaBaselineWithDanglingLogsSymlinkIsRejected() =>
        LeanReportCiBaselineScriptContract.AssertDeltaBaselineWithDanglingLogsSymlinkIsRejected();

    [Fact]
    public void CiBaselineAdapterDoesNotCopyProducerLogsIntoDeltaCache() =>
        LeanReportCiBaselineScriptContract.AssertAdapterDoesNotCopyProducerLogsIntoDeltaCache();
}

internal static class LeanReportCiBaselineScriptContract
{
    private const string ScriptPath = "tools/scripts/report/lean-report-ci-baseline.sh";
    private const string Address = "8b3819495bc2c23d0d68936f67cd83619c8eae2fcb3ee506d00ffb61e2448759";
    private const string Producer = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    private const string Resident = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
    private const string Config = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

    internal static void AssertCanonicalProvenanceBytesAreAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);

        var result = Run(bundle, cache);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(cache, Encoding.UTF8.GetString(result.StandardOutput).Trim());
        Assert.Contains(
            "LEAN_REPORT_CI_BASELINE status=ready",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    internal static void AssertNonCanonicalProvenanceBytesAreRejected(string mutation)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bundle = Path.Combine(temporary.Path, "bundle", "raw-lean-report.json");
        var cache = Path.Combine(temporary.Path, "cache");
        WriteBundle(bundle);
        var provenancePath = bundle + ".provenance.json";
        var canonical = File.ReadAllText(provenancePath, Encoding.UTF8);
        var malformed = mutation switch
        {
            "reordered-keys" => canonical.Replace(
                "{\"schema\":\"stratalint-lean-report-provenance-v1\",\"side\":\"candidate\"",
                "{\"side\":\"candidate\",\"schema\":\"stratalint-lean-report-provenance-v1\"",
                StringComparison.Ordinal),
            "whitespace" => canonical.Replace(
                ",\"side\":\"candidate\"",
                ", \"side\":\"candidate\"",
                StringComparison.Ordinal),
            "duplicate-key" => canonical.Replace(
                "\"side\":\"candidate\",\"mode\"",
                "\"side\":\"candidate\",\"side\":\"candidate\",\"mode\"",
                StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(mutation), mutation, null),
        };
        Assert.NotEqual(canonical, malformed);
        File.WriteAllText(provenancePath, malformed, new UTF8Encoding(false));

        var result = Run(bundle, cache);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Contains(
            "LEAN_REPORT_CI_BASELINE status=fallback reason=invalid-attestation",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(cache, Address)));
    }

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

    private static string RunDeltaPlan(string temporaryPath, string cache)
    {
        var modules = Path.Combine(temporaryPath, "modules.tsv");
        var plan = Path.Combine(temporaryPath, "plan.json");
        File.WriteAllText(modules, string.Empty, new UTF8Encoding(false));
        var delta = TestProcessRunner.Run(
            "python3",
            [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "plan",
                temporaryPath, cache, new string('b', 64), Producer, Resident, Config, modules, plan],
            temporaryPath, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, delta.ExitCode);
        return plan;
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
        using var archive = ZipFile.Open(report + ".materials.zip", ZipArchiveMode.Create);
        var entry = archive.CreateEntry("materials.txt");
        using var writer = new StreamWriter(entry.Open(), new UTF8Encoding(false));
        writer.Write("materials\n");
    }
}
