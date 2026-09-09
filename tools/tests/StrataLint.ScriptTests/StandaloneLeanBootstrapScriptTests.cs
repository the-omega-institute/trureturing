using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class StandaloneLeanBootstrapScriptTests
{
    [Theory]
    [InlineData("lean")]
    [InlineData("lean-cache-ensure")]
    public void StandaloneTargetBuildsMissingProducerAndRefreshesChangedSource(string target)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new BootstrapFixture(target);

        fixture.AssertSuccess(fixture.Make(target));
        Assert.Equal(new[] { "candidate-first" }, fixture.CliCalls);
        Assert.Single(fixture.BuildCalls);
        Assert.Equal(target == "lean" ? new[] { "build" } : [], fixture.LakeCalls);

        fixture.ChangeSource("candidate-second");
        fixture.AssertSuccess(fixture.Make(target));
        Assert.Equal(new[] { "candidate-first", "candidate-second" }, fixture.CliCalls);
        Assert.Equal(2, fixture.BuildCalls.Length);
    }

    [Theory]
    [InlineData("lean")]
    [InlineData("lean-cache-ensure")]
    public void StandaloneTargetPropagatesRealCompilationFailure(string target)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new BootstrapFixture(target);
        fixture.BreakSource();

        var result = fixture.Make(target);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("error CS0103", fixture.Text(result), StringComparison.Ordinal);
        Assert.Empty(fixture.CliCalls);
        Assert.Empty(fixture.LakeCalls);
    }

    [Theory]
    [InlineData("lean", false)]
    [InlineData("lean-cache-ensure", false)]
    [InlineData("lean", true)]
    [InlineData("lean-cache-ensure", true)]
    public void WrapperPreservesProducerFailureAndPrebuiltDispatchDoesNotBuild(string target, bool prebuilt)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new BootstrapFixture(target);
        if (prebuilt) fixture.AssertSuccess(fixture.Make(target));
        var builds = fixture.BuildCalls.Length;

        var result = fixture.Wrapper(target, prebuilt, producerExit: 23);

        Assert.True(result.ExitCode == 23, fixture.Text(result));
        Assert.Equal(builds + (prebuilt ? 0 : 1), fixture.BuildCalls.Length);
        Assert.Equal(prebuilt ? 2 : 1, fixture.CliCalls.Length);
        Assert.Equal(target == "lean" ? fixture.CliCalls.Length : 0, fixture.LakeCalls.Length);
    }

    [Theory]
    [InlineData("lean")]
    [InlineData("lean-cache-ensure")]
    public void MissingExplicitPrebuiltProducerFailsWithoutBootstrapping(string target)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new BootstrapFixture(target);

        var result = fixture.Wrapper(target, prebuilt: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(fixture.BuildCalls);
        Assert.Empty(fixture.CliCalls);
        Assert.Empty(fixture.LakeCalls);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class BootstrapFixture : IDisposable
    {
        private readonly string projectDirectory;
        private readonly string producerDll;
        private readonly string producerVariable;
        private readonly TemporaryDirectory temporary = new();
        private readonly string root;
        private readonly string bin;

        internal BootstrapFixture(string target)
        {
            var projectName = target == "lean" ? "StrataLint.EngineeringScope" : "StrataLint.Cli";
            var assemblyName = target == "lean" ? projectName : "StrataLint";
            projectDirectory = "tools/" + projectName;
            producerDll = projectDirectory + "/bin/Release/net10.0/" + assemblyName + ".dll";
            producerVariable = target == "lean" ? "STRATALINT_LEAN_PRODUCER_DLL" : "STRATALINT_LEAN_CLI_DLL";
            root = Path.Combine(temporary.Path, "candidate with spaces");
            bin = Path.Combine(temporary.Path, "bin");
            ScriptHarnessScratch.EnsureDirectory(bin);
            foreach (var path in new[] { "Makefile", WrapperPath("lean"), WrapperPath("lean-cache-ensure") })
                ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(root, path));
            Write(projectDirectory + "/" + projectName + ".csproj", $$"""
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup>
                    <TargetFramework>net10.0</TargetFramework>
                    <OutputType>Exe</OutputType>
                    <AssemblyName>{{assemblyName}}</AssemblyName>
                    <EnableSourceControlManagerQueries>false</EnableSourceControlManagerQueries>
                  </PropertyGroup>
                  <Target Name="RecordBootstrap" BeforeTargets="Build">
                    <WriteLinesToFile File="$(MSBuildProjectDirectory)/../../bootstrap.log" Lines="build" Overwrite="false" />
                  </Target>
                </Project>
                """);
            ChangeSource("candidate-first");
            WriteExecutable(Path.Combine(bin, "lake"), """
                printf '%s\n' "$*" >> "$LEAN_BOOTSTRAP_ROOT/lake.log"
                exit "$LEAN_BOOTSTRAP_PRODUCER_EXIT"
                """);
            foreach (var command in new[] { "git", "gh" })
                WriteExecutable(Path.Combine(bin, command), "exit 97");
        }

        internal string[] CliCalls => Calls("cli.log");
        internal string[] BuildCalls => Calls("bootstrap.log");
        internal string[] LakeCalls => Calls("lake.log");

        internal void ChangeSource(string marker) => Write(projectDirectory + "/Program.cs", $$"""
            using System;
            using System.Diagnostics;
            using System.IO;
            var root = Environment.GetEnvironmentVariable("LEAN_BOOTSTRAP_ROOT");
            File.AppendAllText(Path.Combine(root, "cli.log"), "{{marker}}\n");
            if (args is ["worktree", "ensure-cache"]) return int.Parse(Environment.GetEnvironmentVariable("LEAN_BOOTSTRAP_PRODUCER_EXIT"));
            if (args.Length < 3 || args[0] != "lean-cache-writer" || args[1] != "--") return 92;
            var start = new ProcessStartInfo(args[2]) { UseShellExecute = false };
            foreach (var argument in args[3..]) start.ArgumentList.Add(argument);
            using var process = Process.Start(start);
            process.WaitForExit();
            return process.ExitCode;
            """);

        internal void BreakSource() => Write(projectDirectory + "/Program.cs", "return MissingBootstrapSymbol;\n");

        internal ProcessOutput Make(string target) => Run(false, 0, "make", "-C", root, target);

        internal ProcessOutput Wrapper(string target, bool prebuilt, int producerExit = 0) => Run(prebuilt, producerExit,
            new[] { "/bin/bash", Path.Combine(root, WrapperPath(target)) }
                .Concat(target == "lean" ? new[] { "lake", "build" } : []).ToArray());

        internal string Text(ProcessOutput result) => Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        internal void AssertSuccess(ProcessOutput result) => Assert.True(result.ExitCode == 0, Text(result));

        private ProcessOutput Run(bool prebuilt, int producerExit, params string[] command) => TestProcessRunner.Run("/usr/bin/env",
            new[]
            {
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"LEAN_BOOTSTRAP_ROOT={root}",
                $"LEAN_BOOTSTRAP_PRODUCER_EXIT={producerExit}",
                $"{producerVariable}={(prebuilt ? Path.Combine(root, producerDll) : "")}",
                "DOTNET_CLI_UI_LANGUAGE=en-US",
            }.Concat(command), temporary.Path, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);

        private string[] Calls(string name) => ScriptHarnessScratch.ReadRecordedCalls(Path.Combine(root, name));
        private static string WrapperPath(string target) => target == "lean"
            ? "tools/scripts/worktree/lean-cache-run.sh" : "tools/scripts/worktree/lean-cache-ensure.sh";

        private void Write(string path, string content)
        {
            var full = Path.Combine(root, path);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(full)!);
            ScriptHarnessScratch.WriteScratchText(full, content);
        }

        private static void WriteExecutable(string path, string body)
        {
            // Process.Start requires a BOM-free shebang for direct script execution.
            ScriptHarnessScratch.WriteScratchText(path, "#!/bin/bash\nset -euo pipefail\n" + body + "\n");
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        public void Dispose() => temporary.Dispose();
    }
}
