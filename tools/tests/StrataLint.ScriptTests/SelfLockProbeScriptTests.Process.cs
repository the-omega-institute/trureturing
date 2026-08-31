using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    private static ProcessOutput RunProbe(
        ProbeFixture fixture,
        IReadOnlyList<string> requiredGates,
        IReadOnlyList<string> redGates)
    {
        if (requiredGates.SequenceEqual(["engineering"]) && redGates.SequenceEqual(["engineering"]))
            return RunEngineeringRedProbe(fixture);
        if (requiredGates.SequenceEqual(["engineering"]) && redGates.Count == 0)
            return RunEngineeringNoRedProbe(fixture);
        if (requiredGates.SequenceEqual(["engineering", "lean"]))
            return RunEngineeringLeanProbe(fixture);
        if (requiredGates.SequenceEqual(["engineering", "admission"]))
            return RunEngineeringAdmissionProbe(fixture);
        throw new ArgumentException("unsupported test gate combination");
    }

    private static ProcessOutput RunEngineeringRedProbe(ProbeFixture fixture) =>
        RunController(fixture, ["--required-gate", "engineering", "--red-gate", "engineering"]);

    private static ProcessOutput RunEngineeringNoRedProbe(ProbeFixture fixture) =>
        RunController(fixture, ["--required-gate", "engineering"]);

    private static ProcessOutput RunEngineeringLeanProbe(ProbeFixture fixture) =>
        RunController(
            fixture,
            ["--required-gate", "engineering", "--required-gate", "lean", "--red-gate", "engineering"]);

    private static ProcessOutput RunEngineeringAdmissionProbe(ProbeFixture fixture) =>
        RunController(
            fixture,
            ["--required-gate", "engineering", "--required-gate", "admission", "--red-gate", "engineering"]);

    private static ProcessOutput RunController(
        ProbeFixture fixture,
        IReadOnlyList<string> gateArguments) =>
        TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "evaluate",
                "--controller-root", TestRepositoryLayout.FindRoot(),
                "--pure-revert-script", Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "scripts",
                    "workflow",
                    "pure-revert-detect.sh"),
                "--candidate-repository", fixture.CandidateRepository,
                "--j1-repository", fixture.J1Repository,
                "--j1-bundle", fixture.J1Bundle.Path,
                "--j0-repository", fixture.J0Repository,
                "--j0-bundle", fixture.J0Bundle.Path,
                .. gateArguments,
            ],
            TestRepositoryLayout.FindRoot(),
            TestBudgets.ScriptProcessHangGuard,
            256 * 1024);

    private static ProcessOutput RunControllerWithClassifier(
        ProbeFixture fixture,
        string classifier) =>
        TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "evaluate",
                "--controller-root", TestRepositoryLayout.FindRoot(),
                "--pure-revert-script", classifier,
                "--candidate-repository", fixture.CandidateRepository,
                "--j1-repository", fixture.J1Repository,
                "--j1-bundle", fixture.J1Bundle.Path,
                "--j0-repository", fixture.J0Repository,
                "--j0-bundle", fixture.J0Bundle.Path,
                "--required-gate", "engineering",
                "--red-gate", "engineering",
            ],
            TestRepositoryLayout.FindRoot(),
            TestBudgets.ScriptProcessHangGuard,
            256 * 1024);

    private static string ReadControllerDigest()
    {
        var result = TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "evaluator-digest",
                "--controller-root",
                TestRepositoryLayout.FindRoot(),
            ],
            TestRepositoryLayout.FindRoot(),
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static PublishedBundle PublishBundle(string bundleRoot, string stagingBundle)
    {
        var result = TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "publish",
                "--controller-root", TestRepositoryLayout.FindRoot(),
                "--bundle-root", bundleRoot,
                "--staging-bundle", stagingBundle,
            ],
            TestRepositoryLayout.FindRoot(),
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        return System.Text.Json.JsonSerializer.Deserialize<PublishedBundle>(
            result.StandardOutput,
            JsonOptions) ?? throw new InvalidOperationException("publisher output was empty");
    }

    private static string DigestScratchFile(string path)
    {
        var result = TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "artifact-digest",
                "--path", path,
            ],
            TestRepositoryLayout.FindRoot(),
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static void TamperReceiptProducer(string path)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/perl",
            [
                "-pi", "-e",
                "s/\"producer_sha256\":\"sha256:[0-9a-f]{64}\"/\"producer_sha256\":\"sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\"/",
                path,
            ],
            System.IO.Path.GetDirectoryName(path)!,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
    }

    private static void TamperPointerSentinel(string path)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/perl",
            [
                "-pi", "-e",
                "s/\"sentinel_sha256\":\"sha256:[0-9a-f]{64}\"/\"sentinel_sha256\":\"sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee\"/",
                path,
            ],
            System.IO.Path.GetDirectoryName(path)!,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
    }
}
