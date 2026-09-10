using System.Diagnostics;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class NegativeProofStageTests
{
    public static TheoryData<string, int, int> RejectedExits()
    {
        var data = new TheoryData<string, int, int>();
        foreach (var proof in new[] { "capability-proof", "banned-api-proof" })
        foreach (var raw in new[] { 0, 2, 3, 19, 124, 127, 255 })
            data.Add(proof, raw, raw == 0 ? 1 : 2);
        return data;
    }

    [Theory]
    [MemberData(nameof(RejectedExits))]
    public async Task UnexpectedExitRetainsRawValueAndCannotProveRejection(string proof, int raw, int expected)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var bin = Path.Combine(fixture.Root, "build", "bin");
        TemporaryFileSystem.Directory.CreateDirectory(bin);
        var shim = Path.Combine(bin, "dotnet");
        TemporaryFileSystem.File.WriteAllText(shim, """
            #!/bin/bash
            if [[ "$1" == build && "$2" == */CompileFailProof/CompileFailProof.csproj ]]; then
              printf 'MissingCapability.cs(13,9): error CS7036: missing metaClear\n'
              [[ "$CONTRACT_PROOF" == capability-proof ]] && exit "$CONTRACT_RAW"
              exit 1
            fi
            if [[ "$1" == build && "$2" == */BannedApiCompileFailProof/BannedApiCompileFailProof.csproj ]]; then
              printf 'BannedApiViolations.cs(1,1): error RS0030: banned symbol\n'
              exit "$CONTRACT_RAW"
            fi
            exit 0
            """);
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var source = Path.Combine(fixture.Root, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        TemporaryFileSystem.File.WriteAllText(source, "// banned-api-proof\n");
        const string log = "build/ci/proof-fixture.log";
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, "build/ci"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, log), "synthetic build\n");
        var build = CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), [log],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
        var start = new ProcessStartInfo(Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope"))
        {
            WorkingDirectory = fixture.Root, RedirectStandardOutput = true, RedirectStandardError = true,
        };
        start.ArgumentList.Add("engineering");
        start.ArgumentList.Add("--repository");
        start.ArgumentList.Add(fixture.Root);
        start.ArgumentList.Add("--build-round");
        start.ArgumentList.Add(build.Round);
        start.Environment.Remove("PREFLIGHT_DEADLINE_AT");
        start.Environment["PATH"] = bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH");
        start.Environment["CONTRACT_PROOF"] = proof;
        start.Environment["CONTRACT_RAW"] = raw.ToString(System.Globalization.CultureInfo.InvariantCulture);
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        try
        {
            Assert.True(process.WaitForExit((int)TestBudgets.ScriptProcessHangGuard.TotalMilliseconds));
            var output = await stdout + await stderr;
            Assert.True(process.ExitCode == expected, output);
            using var summary = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
                Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "engineering-result.json")));
            var step = summary.RootElement.GetProperty("steps").EnumerateArray().Last();
            Assert.Equal(proof, step.GetProperty("name").GetString());
            Assert.Equal(raw, step.GetProperty("raw_exit").GetInt32());
            Assert.Equal(expected, step.GetProperty("exit").GetInt32());
            Assert.Equal("failed", step.GetProperty("status").GetString());
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.EngineeringPath)));
        }
        finally
        {
            if (!process.HasExited) { process.Kill(entireProcessTree: true); process.WaitForExit(); }
        }
    }
}
