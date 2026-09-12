using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    [Fact]
    public void AddressIsIndependentOfCallerWorkingDirectorySdk()
    {
        using var fixture = new LeanReportInputFixture();
        var fromRepository = fixture.AddressFromRepository();
        var fromForeignSdk = fixture.AddressFromForeignSdkDirectory();
        Assert.Equal(0, fromRepository.ExitCode);
        Assert.Equal(fromRepository.ExitCode, fromForeignSdk.ExitCode);
        Assert.Equal(fromRepository.StandardOutput, fromForeignSdk.StandardOutput);
    }

    [Fact]
    public void AddressDoesNotEvaluateDotnetProjectsOrSdk()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Address();
        fixture.UseUnavailableRepositorySdk();
        fixture.Append(CliProjectPath, "<");
        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void AddressMatchesIndependentVersionOnlyPreimage()
    {
        using var fixture = new LeanReportInputFixture();
        var result = fixture.AddressFromRepository();
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.ExpectedAddressBytes(), result.StandardOutput);
        Assert.Empty(result.StandardError);
    }

    private sealed partial class LeanReportInputFixture
    {
        private const string UnavailableSdk =
            "{\"sdk\":{\"version\":\"99.0.100\",\"rollForward\":\"disable\"}}\n";

        internal ProcessOutput AddressFromRepository() => Run("address", repository);
        internal void RemoveSource(string relativePath) => File.Delete(Path.Combine(repository, relativePath));
        internal ProcessOutput AddressFromForeignSdkDirectory()
        {
            var directory = Path.Combine(temporary.Path, "foreign sdk");
            Directory.CreateDirectory(directory);
            File.WriteAllText(Path.Combine(directory, "global.json"), UnavailableSdk);
            return Run("address", directory);
        }

        internal void UseUnavailableRepositorySdk() => Write("global.json", UnavailableSdk);
        internal ProcessOutput CompiledCacheAddress()
        {
            var result = TestProcessRunner.Run("env",
                [$"STRATALINT_LEAN_INPUT_MEMO_ROOT={MemoRoot}", "bash",
                    Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-input.sh"),
                    "address", "--repository", repository], temporary.Path,
                BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return result;
        }

        internal byte[] ExpectedAddressBytes()
        {
            // Independently fixed contract preimage, never derived from the helper's output.
            var producer = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
                "schema=stratalint-lean-report-compatibility\nversion=1\n")));
            var sources = ManifestHash("Trureturing.lean", "D5/Probe.lean");
            var config = ManifestHash("lean-toolchain", "lake-manifest.json", "lakefile.toml");
            var preimage = "schema=stratalint-lean-report-repository-input-v1\n"
                + $"repository_inspector_sha256={producer}\n"
                + $"lean_sources_sha256={sources}\nlean_config_sha256={config}\n";
            var address = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(preimage)));
            return Encoding.UTF8.GetBytes($"{address} {producer} {sources} {config}\n");
        }
    }
}
