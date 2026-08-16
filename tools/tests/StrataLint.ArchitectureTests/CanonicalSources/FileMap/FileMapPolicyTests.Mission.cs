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
        AssertGovernanceMutationSurfacesAsMissionContractFinding(
            "stratalint-mission-task-",
            static (target, taskStart, nextTaskStart) =>
                target[..taskStart]
                + "def staleMissionMarker : String := \"TASK D5-T0040\"\n\n"
                + target[nextTaskStart..]);
    }

    [Fact]
    public void NumeralAdjacentRawStringTaskMarkerSurfacesAsMissionContractFinding()
    {
        AssertGovernanceMutationSurfacesAsMissionContractFinding(
            "stratalint-mission-raw-task-",
            static (target, taskStart, nextTaskStart) => target[..taskStart] + """
                def staleMissionMarker := 1r##"
                An unescaped " does not close this raw string.
                /-- TASK D5-T0040
                    This text is inside a numeral-adjacent raw string. -/
                "## -- " keeps the legacy scanner synchronized after the raw terminator.

                """ + target[nextTaskStart..]);
    }

    [Fact]
    public void PrimedIdentifierHiddenDuplicateSurfacesAsMissionContractFinding()
    {
        AssertGovernanceMutationSurfacesAsMissionContractFinding(
            "stratalint-mission-prime-task-",
            static (target, _, _) => target + "\n" + """
                def separator' : Unit := ()
                /-- TASK D5-T0040
                    This duplicate follows a primed identifier. -/
                def duplicateMissionNoveltyTicket : Unit := ()
                """);
    }

    [Fact]
    public void GuessedRawTerminatorRecoverySurfacesAsMissionContractFinding()
    {
        AssertGovernanceMutationSurfacesAsMissionContractFinding(
            "stratalint-mission-raw-recovery-task-",
            static (target, taskStart, nextTaskStart) =>
                target[..taskStart] + target[nextTaskStart..] + "\n" + """
                def x := identifierr##"
                inside "
                "##
                /-- TASK D5-T0040
                    This block is inert under the correct lexical state. -/
                "
                """);
    }

    private static void AssertGovernanceMutationSurfacesAsMissionContractFinding(
        string fixturePrefix,
        Func<string, int, int, string> mutation)
    {
        var fixture = Directory.CreateTempSubdirectory(fixturePrefix);
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
            foreach (var relativePath in new[]
                     {
                         MissionFileLoader.RelativePath,
                         "Meta/Digestion/ticket-index.toml",
                         "D5/X_Frontier/GovernanceDeferrals.lean",
                     })
            {
                File.Copy(
                    Path.Combine(RepositoryLayout.FindRoot(), relativePath),
                    Path.Combine(repository, relativePath),
                    overwrite: true);
                RunMissionGit(repository, "add", "--", relativePath);
            }

            const string targetRelativePath = "D5/X_Frontier/GovernanceDeferrals.lean";
            var targetPath = Path.Combine(repository, targetRelativePath);
            var target = RunMissionGit(repository, "show", $":{targetRelativePath}");
            var taskStart = target.IndexOf("/-- TASK D5-T0040\n", StringComparison.Ordinal);
            var nextTaskStart = target.IndexOf("/-- TASK D5-T0041\n", StringComparison.Ordinal);
            Assert.True(taskStart >= 0 && nextTaskStart > taskStart);
            target = mutation(target, taskStart, nextTaskStart);
            File.WriteAllText(targetPath, target, new UTF8Encoding(false));

            var finding = Assert.Single(
                FileMapPolicy.InspectRepository(repository),
                static finding => finding.Code == "MISSION-CONTRACT");

            Assert.Equal(MissionFileLoader.RelativePath, finding.Path);
            Assert.Contains(
                nameof(MissionLoadErrorCode.DanglingCaseReference),
                finding.Message,
                StringComparison.Ordinal);
            Assert.Contains("D5-T0040", finding.Message, StringComparison.Ordinal);
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
            foreach (var relativePath in new[]
                     {
                         MissionFileLoader.RelativePath,
                         "Meta/Digestion/ticket-index.toml",
                         "D5/X_Frontier/GovernanceDeferrals.lean",
                     })
            {
                File.Copy(
                    Path.Combine(RepositoryLayout.FindRoot(), relativePath),
                    Path.Combine(repository, relativePath),
                    overwrite: true);
                RunMissionGit(repository, "add", "--", relativePath);
            }
            var missionPath = Path.Combine(repository, MissionFileLoader.RelativePath);
            var mission = RunMissionGit(
                repository,
                "show",
                $":{MissionFileLoader.RelativePath}");
            foreach (var (factor, caseId) in new[]
                     {
                         ("novelty", "D5-T0040"),
                         ("dependency_readiness", "D5-T0041"),
                         ("structural_realization", "D5-T0042"),
                         ("receipt_potential", "D5-T0043"),
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
            Assert.Contains("D5-T0040", finding.Message, StringComparison.Ordinal);
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
