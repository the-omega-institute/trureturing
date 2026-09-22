using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.EngineeringScope;
using Xunit;
using static StrataLint.TestSupport.ExecutionFixture;

namespace StrataLint.TestSupport;

internal static class TransportFixture
{
    internal const string Log = "build/ci/fixture-executable";
    internal static StageStep[] Steps(string[] names) => names.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", Log)).ToArray();

    internal static void PrepareCurrentRuntime(ExecutionFixture fixture)
    {
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(TestRepositoryLayout.FindRoot(), runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    internal static void Prepare(ExecutionFixture fixture, bool current)
    {
        fixture.Build();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, Log), "#!/bin/sh\nexit 0\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Root, Log), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        SealEngineering(fixture.Root, candidate, [Log], Steps(CommonExecutionEvidence.EngineeringSteps));
        if (!current) return;
        Report(fixture.Root);
        CheckEvidenceFixture.Seal(fixture.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Root));
        CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    internal static void SealEngineering(string root, string candidate, IEnumerable<string> binaries, StageStep[] steps)
    {
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(candidate, build.Candidate);
        build = build with { Materials = CommonExecutionEvidence.Materials(root,
            build.Materials.Select(material => material.Path).Concat(binaries)) };
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.BuildPath, build);
        var list = CommonExecutionEvidence.BundleListPath("build");
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, list), string.Join('\0',
            build.Materials.Select(material => material.Path).Append(CommonExecutionEvidence.BuildPath).Append(list)
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)) + "\0");
        CheckEvidenceFixture.Seal(root, "engineering", build);
        CommonExecutionEvidence.SealEngineering(root, build, steps);
    }

    internal static int Run(string command, string root, string stage, string commit, string run, string attempt, string? archive = null) =>
        Program.Run(new[] { command, "--repository", root, "--stage", stage, "--commit", commit, "--run-id", run, "--run-attempt", attempt }
            .Concat(archive is null ? [] : new[] { "--archive", archive }).ToArray(), TestResultEvidence.Load, TextWriter.Null, TextWriter.Null);

    internal static string Git(string root, params string[] args)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var arg in args) start.ArgumentList.Add(arg);
        using var process = Process.Start(start)!;
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, error);
        return output.Trim();
    }
}
