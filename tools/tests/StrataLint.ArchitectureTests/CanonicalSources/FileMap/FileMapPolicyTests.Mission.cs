using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void NonBlockTaskMarkerSurfacesAsMissionContractFinding()
    {
        var fixture = Directory.CreateTempSubdirectory("stratalint-mission-task-");
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
            const string targetRelativePath = "D5/X_Frontier/GovernanceDeferrals.lean";
            var targetPath = Path.Combine(repository, targetRelativePath);
            var target = RunMissionGit(repository, "show", $"HEAD:{targetRelativePath}");
            var taskStart = target.IndexOf("/-- TASK D5-T0039 |", StringComparison.Ordinal);
            var nextTaskStart = target.IndexOf("/-- TASK D5-T0040 |", StringComparison.Ordinal);
            Assert.True(taskStart >= 0 && nextTaskStart > taskStart);
            target = target[..taskStart]
                + "def staleMissionMarker : String := \"TASK D5-T0039 |\"\n\n"
                + target[nextTaskStart..];
            File.WriteAllText(targetPath, target, new UTF8Encoding(false));

            var finding = Assert.Single(
                FileMapPolicy.InspectRepository(repository),
                static finding => finding.Code == "MISSION-CONTRACT");

            Assert.Equal(MissionFileLoader.RelativePath, finding.Path);
            Assert.Contains(
                nameof(MissionLoadErrorCode.DanglingCaseReference),
                finding.Message,
                StringComparison.Ordinal);
            Assert.Contains("D5-T0039", finding.Message, StringComparison.Ordinal);
        }
        finally
        {
            fixture.Delete(recursive: true);
        }
    }

    private static void AssertInventedMeasuredReceiptsSurfaceAsMissionContractFinding()
    {
        var fixture = Directory.CreateTempSubdirectory("stratalint-mission-");
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
                $"HEAD:{MissionFileLoader.RelativePath}");
            foreach (var (factor, caseId) in new[]
                     {
                         ("novelty", "D5-T0039"),
                         ("dependency_readiness", "D5-T0040"),
                         ("structural_realization", "D5-T0041"),
                         ("receipt_potential", "D5-T0042"),
                     })
            {
                mission = mission.Replace(
                    $"\"{factor}\": {{ \"state\": \"open\", \"case_id\": \"{caseId}\" }}",
                    $"\"{factor}\": {{ \"state\": \"measured\", \"value\": 1.25, \"receipt_ref\": \"receipt:invented:{factor}\" }}",
                    StringComparison.Ordinal);
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
            Assert.Contains("D5-T0039", finding.Message, StringComparison.Ordinal);
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
