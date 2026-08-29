using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void InventedMeasuredReceiptsSurfaceThroughFileMapMissionContractFinding()
    {
        var fixture = Directory.CreateTempSubdirectory("stratalint-filemap-mission-");
        try
        {
            var repository = Path.Combine(fixture.FullName, "repository");
            RunMissionGit(
                fixture.FullName,
                "clone",
                "--quiet",
                "--no-hardlinks",
                RepositoryLayout.FindRoot(),
                repository);
            var missionPath = Path.Combine(repository, MissionFileLoader.RelativePath);
            var mission = RunMissionGit(
                repository,
                "show",
                $":{MissionFileLoader.RelativePath}");
            foreach (var factor in new[]
                     {
                         "novelty",
                         "dependency_readiness",
                         "structural_realization",
                         "receipt_potential",
                     })
            {
                var open = $"\"{factor}\": {{ \"state\": \"open\" }}";
                var measured =
                    $"\"{factor}\": {{ \"state\": \"measured\", \"value\": 1.25, "
                    + $"\"receipt_ref\": \"receipt:invented:{factor}\" }}";
                var changed = mission.Replace(open, measured, StringComparison.Ordinal);
                Assert.NotEqual(mission, changed);
                mission = changed;
            }

            mission = mission.Replace(
                "bootstrap eligibility order",
                "complete worth argmax",
                StringComparison.Ordinal);
            File.WriteAllText(missionPath, mission, new UTF8Encoding(false));

            var finding = Assert.Single(
                FileMapPolicy.InspectRepository(repository),
                static finding => finding.Code == "MISSION-CONTRACT");

            Assert.Equal(MissionFileLoader.RelativePath, finding.Path);
            Assert.Contains(
                nameof(MissionLoadErrorCode.InvalidWorthState),
                finding.Message,
                StringComparison.Ordinal);
            Assert.Contains(
                "worth_vector.novelty measured is fail-closed in P0",
                finding.Message,
                StringComparison.Ordinal);
        }
        finally
        {
            fixture.Delete(recursive: true);
        }
    }

    private static string RunMissionGit(string workingDirectory, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = workingDirectory,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("failed to start git");
        process.WaitForExit();
        var standardOutput = process.StandardOutput.ReadToEnd();
        var standardError = process.StandardError.ReadToEnd();
        Assert.True(process.ExitCode == 0, standardError);
        return standardOutput;
    }
}
