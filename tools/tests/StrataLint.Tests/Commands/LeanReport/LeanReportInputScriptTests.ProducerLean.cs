using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    [Fact]
    public void SupportingLeanEditRejectsProducerBaselineReuse()
    {
        using var fixture = new LeanReportInputFixture();
        const string supporting = "tools/lean-inspector/LeanInformationAudit/Nested/Registry.lean";
        fixture.WriteSource(supporting, "def companion := 1\n");
        fixture.CreateDeltaBaseline();
        Assert.Equal("reuse", fixture.DeltaPlanStatus());
        fixture.WriteSource("tools/lean-inspector/README.md", "documentation only\n");
        Assert.Equal("reuse", fixture.DeltaPlanStatus());
        fixture.Append(supporting, "def changedCompanion := 2\n");
        Assert.Equal("fallback", fixture.DeltaPlanStatus());
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void ProducerClosureIncludesNestedLeanOnly(string command)
    {
        using var fixture = new LeanReportInputFixture();
        const string source = "tools/lean-inspector/LeanInformationAudit/Nested/Registry.lean";
        const string readme = "tools/lean-inspector/README.md";
        fixture.WriteSource(source, "def companion := 1\n");
        fixture.WriteSource(readme, "documentation only\n");
        var result = fixture.RunCommand(command);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(source, Lines(result));
        Assert.DoesNotContain(readme, Lines(result));
    }

    private sealed partial class LeanReportInputFixture
    {
        private string DeltaCache => Path.Combine(temporary.Path, "delta-cache");
        private string ModuleTable => Path.Combine(temporary.Path, "modules.tsv");

        internal void CreateDeltaBaseline()
        {
            var result = RunCommand("address");
            Assert.Equal(0, result.ExitCode);
            var fields = Fields(result);
            // A different complete input address with identical module inputs is
            // the planner's normal zero-recheck baseline-reuse case.
            var baselineAddress = new string(fields[0][0] == 'a' ? 'b' : 'a', 64);
            var entry = Path.Combine(DeltaCache, baselineAddress);
            Directory.CreateDirectory(entry);
            var baseline = Path.Combine(entry, "raw-lean-report.json");
            var modules = new[] { ("Trureturing", "Trureturing.lean"), ("D5.Probe", "D5/Probe.lean") };
            File.WriteAllText(ModuleTable, string.Concat(modules.Select(row => $"{row.Item1}\t{row.Item2}\n")));
            var reportBytes = JsonSerializer.SerializeToUtf8Bytes(new
            {
                schema = "stratalint-raw-lean-report-v2",
                modules = modules.Select(row => new
                {
                    module = row.Item1, source_path = row.Item2,
                    source_sha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(
                        File.ReadAllBytes(Path.Combine(repository, row.Item2)))),
                    imports = Array.Empty<string>(), declarations = Array.Empty<object>(),
                }),
            });
            File.WriteAllBytes(baseline, reportBytes);
            var sha = Convert.ToHexStringLower(SHA256.HashData(reportBytes));
            File.WriteAllText(baseline + ".sha256", $"{sha}  raw-lean-report.json\n");
            using (ZipFile.Open(baseline + ".materials.zip", ZipArchiveMode.Create)) { }
            File.WriteAllText(baseline + ".input.attestation",
                "schema=stratalint-lean-report-input-attestation-v1\n"
                + $"repository_input_sha256={baselineAddress}\nproducer_sha256={fields[1]}\nreport_sha256={sha}\n");
            File.WriteAllText(baseline + ".provenance.json", JsonSerializer.Serialize(new
            {
                schema = "stratalint-lean-report-provenance-v1", side = "candidate", mode = "produced",
                source_side = "candidate", input_address = "sha256:" + baselineAddress,
                producer_sha256 = fields[1], repository_inspector_sha256 = fields[1],
                lean_sources_sha256 = fields[2], lean_config_sha256 = fields[3], report_sha256 = sha,
            }));
        }

        internal string DeltaPlanStatus()
        {
            var address = RunCommand("address");
            Assert.Equal(0, address.ExitCode);
            var fields = Fields(address);
            var plan = Path.Combine(temporary.Path, "plan.json");
            var result = TestProcessRunner.Run("python3",
                [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/delta.py"), "plan",
                 repository, DeltaCache, fields[0], fields[1], fields[1], fields[3], ModuleTable, plan],
                repository, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            using var document = JsonDocument.Parse(File.ReadAllBytes(plan));
            return document.RootElement.GetProperty("status").GetString()!;
        }
    }
}
