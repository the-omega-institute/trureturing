using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PinnedInspectorRuntimeTests
{
    [Fact]
    public void CandidateInspectorReportsKernelFactsUsingCandidateToolchainWithoutTreeReport()
    {
        var root = TestRepositoryLayout.FindRoot();
        using var scratch = new TemporaryDirectory();
        var pin = File.ReadAllText(Path.Combine(root, "lean-toolchain")).Trim();
        const string source = "theorem fixture_closed : (1 : Nat) = 1 := rfl\ntheorem fixture_open : False := by sorry\n";
        File.WriteAllText(Path.Combine(scratch.Path, "Probe.lean"), source);
        File.WriteAllText(Path.Combine(scratch.Path, "Inspector.lean"), File.ReadAllText(Path.Combine(root, "tools/lean-inspector/Inspector.lean")));
        Run("lean", "-o", "Probe.olean", "Probe.lean");
        Run("lean", "--run", "Inspector.lean", "--output", "report.json", "--material-spool", "materials", "Probe", "Probe.lean",
            "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source))));
        using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(scratch.Path, "report.json")));
        var module = Assert.Single(report.RootElement.GetProperty("modules").EnumerateArray());
        var declarations = module.GetProperty("declarations").EnumerateArray().ToArray();
        var closed = Assert.Single(declarations, declaration => declaration.GetProperty("name").GetString() == "fixture_closed");
        Assert.Empty(closed.GetProperty("axioms").EnumerateArray());
        var open = Assert.Single(declarations, declaration => declaration.GetProperty("name").GetString() == "fixture_open");
        Assert.Contains(open.GetProperty("axioms").EnumerateArray(), axiom => axiom.GetString() == "sorryAx");
        Assert.NotEmpty(Directory.GetFiles(Path.Combine(scratch.Path, "materials")));

        void Run(params string[] arguments)
        {
            var result = TestProcessRunner.Run("/bin/bash", new[] { "-c", "export LEAN_PATH=\"$1\"; shift; exec elan run \"$@\"", "pinned-inspector", scratch.Path, pin }.Concat(arguments).ToArray(),
                scratch.Path, TimeSpan.FromMinutes(2), 4 * 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        }
    }
}
