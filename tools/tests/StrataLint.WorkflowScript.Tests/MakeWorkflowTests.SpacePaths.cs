using System.Runtime.Versioning;
using System.Text;
using StrataLint.Runtime;
using static StrataLint.TestSupport.TestExecutable;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("test", "")]
    [InlineData("test", "selected tests/Probe.csproj")]
    [InlineData("test", "tools/selected tests/Probe.csproj")]
    [InlineData("test", "/selected tests/Probe.csproj")]
    [InlineData("check-fast", "")]
    [InlineData("selftest", "")]
    [InlineData("update-renderer-contract", "")]
    [UnsupportedOSPlatform("windows")]
    public void ToolsEntrypointsPreserveArgumentsInRepositoryPathsWithSpaces(string target, string project)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = Path.Combine(temporary.Path, "repository with spaces");
        Directory.CreateDirectory(root);
        var physicalRoot = TestProcessRunner.Run("/bin/pwd", ["-P"], root,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.True(physicalRoot.ExitCode == 0, Encoding.UTF8.GetString(physicalRoot.StandardError));
        root = Encoding.UTF8.GetString(physicalRoot.StandardOutput).TrimEnd('\r', '\n');
        var tools = Path.Combine(root, "tools");
        Directory.CreateDirectory(tools);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), ToolsMakefilePath), Path.Combine(tools, "Makefile"));
        var scriptName = target switch
        {
            "selftest" => "stratalint-selftest.sh",
            "update-renderer-contract" => "update-renderer-contract.sh",
            _ => "dotnet-test.sh",
        };
        WriteExecutable(Path.Combine(tools, "scripts", scriptName), """
            #!/bin/bash
            : > "$DISPATCH_ARGUMENTS"
            if [[ "$#" -gt 0 ]]; then printf '%s\0' "$@" > "$DISPATCH_ARGUMENTS"; fi
            """);
        var log = Path.Combine(temporary.Path, "arguments");
        const string filter = "FullyQualifiedName=Probe.First|FullyQualifiedName=Probe.Second";
        var result = TestProcessRunner.Run("/usr/bin/env",
            ["-u", "MAKEFLAGS", "-u", "MAKEOVERRIDES", "-u", "TEST_PROJECT", "-u", "TEST_FILTER",
             $"DISPATCH_ARGUMENTS={log}", $"DOTNET_ROOT={temporary.Path}",
             "make", "--no-print-directory", "-C", tools, target,
             .. project.Length > 0 ? new[] { $"TEST_PROJECT={project}" } : Array.Empty<string>(),
             $"TEST_FILTER={(project.Length > 0 ? filter : "")}"],
            root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var arguments = File.ReadAllText(log).Split('\0', StringSplitOptions.RemoveEmptyEntries);
        if (target is "selftest" or "update-renderer-contract")
        {
            Assert.Empty(arguments);
            return;
        }
        var expectedProject = project.Length == 0 ? Path.Combine(tools, "StrataLint.sln")
            : project.StartsWith("tools/", StringComparison.Ordinal) ? Path.Combine(root, project) : project;
        Assert.Equal(Path.GetFullPath(expectedProject, root), Path.GetFullPath(arguments[0], root));
        if (target == "check-fast")
        {
            Assert.Equal(3, arguments.Length);
            Assert.Equal("--filter", arguments[1]);
            Assert.Contains("FullyQualifiedName~StrataLint.Tests.CapacityAuditCommandTests", arguments[2], StringComparison.Ordinal);
            Assert.Contains("|FullyQualifiedName~StrataLint.ArchitectureTests.RepositoryIoAccessPolicyTests", arguments[2], StringComparison.Ordinal);
        }
        else
        {
            Assert.Equal(project.Length > 0 ? new[] { arguments[0], "--filter", filter } : new[] { arguments[0] }, arguments);
        }
    }
}
