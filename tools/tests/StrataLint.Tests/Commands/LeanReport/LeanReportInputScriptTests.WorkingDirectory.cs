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

    [Theory]
    [InlineData("msbuild")]
    [InlineData("sdk")]
    public void AddressFailurePreservesProjectAndRawDiagnostic(string failure)
    {
        using var fixture = new LeanReportInputFixture();
        if (failure == "msbuild") fixture.BreakProducerClosureEvaluation();
        else fixture.UseUnavailableRepositorySdk();
        var raw = fixture.EvaluateCliProject();
        Assert.NotEqual(0, raw.ExitCode);
        Assert.NotEmpty(raw.StandardOutput.Concat(raw.StandardError));

        var result = fixture.AddressFromRepository();

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains(fixture.CliProject, diagnostic, StringComparison.Ordinal);
        foreach (var stream in new[] { raw.StandardOutput, raw.StandardError })
        {
            if (stream.Length > 0)
                Assert.Contains(Encoding.UTF8.GetString(stream), diagnostic, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AddressFromRepositoryMatchesIndependentPrechangeBytes()
    {
        using var fixture = new LeanReportInputFixture();

        var result = fixture.AddressFromRepository();

        Assert.Equal(0, result.ExitCode);
        var expected = fixture.ExpectedAddressBytes();
        if (!expected.SequenceEqual(result.StandardOutput))
            Assert.Fail($"Expected: {Encoding.UTF8.GetString(expected)}"
                + $"Actual: {Encoding.UTF8.GetString(result.StandardOutput)}"
                + $"Inputs: {Encoding.UTF8.GetString(fixture.RunCommand("producer-paths").StandardOutput)}");
        Assert.Empty(result.StandardError);
    }

    private sealed partial class LeanReportInputFixture
    {
        private const string UnavailableSdk =
            "{\"sdk\":{\"version\":\"99.0.100\",\"rollForward\":\"disable\"}}\n";

        internal string CliProject
        {
            get
            {
                var physicalPath = TestProcessRunner.Run(
                    "pwd", ["-P"], repository,
                    BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
                Assert.Equal(0, physicalPath.ExitCode);
                return Path.Combine(
                    Encoding.UTF8.GetString(physicalPath.StandardOutput).TrimEnd('\r', '\n'),
                    CliProjectPath);
            }
        }

        internal ProcessOutput AddressFromRepository() => Run("address", repository);

        internal ProcessOutput AddressFromForeignSdkDirectory()
        {
            var directory = Path.Combine(temporary.Path, "foreign sdk");
            Directory.CreateDirectory(directory);
            File.WriteAllText(Path.Combine(directory, "global.json"), UnavailableSdk);
            return Run("address", directory);
        }

        internal void UseUnavailableRepositorySdk() => Write("global.json", UnavailableSdk);

        internal ProcessOutput EvaluateCliProject() => TestProcessRunner.Run(
            "dotnet",
            ["msbuild", CliProject, "-getItem:Compile", "-verbosity:quiet", "-nologo"],
            repository,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        internal byte[] ExpectedAddressBytes()
        {
            // The synthetic fixture's inputs are independent of the helper's output.
            string[] producerPaths =
            [
                "tools/StrataLint.Cli/Commands/FixtureProbe.cs",
                RawReportPath, CanonicalWriterPath, LeanModelsPath,
                CliProjectPath, EngineProjectPath, TruthProjectPath,
                "Directory.Build.props", "Directory.Packages.props", "global.json",
                inspectorScriptPath, inspectorSourcePath, InputHelperPath,
                PairScriptPath, SupervisorScriptPath, CiBaselineScriptPath,
                CacheEnsureScriptPath, CachePublishScriptPath,
                ResourceObservationLibraryPath, ToolchainInstallerPath,
                JudgeContentAddressPath, ScribeContentChecksPath, WorkflowPath,
                EngineLockPath, CliLockPath, TruthLockPath,
            ];
            var producerManifest = string.Concat(producerPaths.Select(path =>
                $"{Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(Path.Combine(repository, path))))}  {path}\n")
                .Order(StringComparer.Ordinal));
            var producer = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(producerManifest)));
            var sources = ManifestHash("Trureturing.lean", "D5/Probe.lean", inspectorSourcePath);
            var config = ManifestHash("lean-toolchain", "lake-manifest.json", "lakefile.toml");
            var preimage = "schema=stratalint-lean-report-repository-input-v1\n"
                + $"repository_inspector_sha256={producer}\n"
                + $"lean_sources_sha256={sources}\nlean_config_sha256={config}\n";
            var address = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(preimage)));
            return Encoding.UTF8.GetBytes($"{address} {producer} {sources} {config}\n");
        }
    }
}
