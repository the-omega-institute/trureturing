using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    internal static void CopyBatchProducerInputs(string root)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.CopyBatchInputs(root);
    }

    internal static void AttestBatchReport(string root, string report)
    {
        var result = TestProcessRunner.Run("/bin/bash",
            [Path.Combine(root, InputHelperPath), "address", "--repository", root], root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var fields = Fields(result);
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

    private sealed partial class LeanReportInputFixture
    {
        internal void CopyBatchInputs(string root)
        {
            foreach (var path in TemporaryFileSystem.Directory.EnumerateFiles(repository, "*", SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(repository, path).Replace('\\', '/');
                if (relative.StartsWith("D5/", StringComparison.Ordinal)
                    || relative.StartsWith("Blueprint/", StringComparison.Ordinal)
                    || relative == "Trureturing.lean") continue;
                var destination = Path.Combine(root, relative);
                if (TemporaryFileSystem.File.Exists(destination)) continue;
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                TemporaryFileSystem.File.WriteAllBytes(destination, TemporaryFileSystem.File.ReadAllBytes(path));
            }
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, InputHelperPath),
                File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), InputHelperPath)));
        }
    }
}
