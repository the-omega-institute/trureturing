using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class UtilityDepositEntryTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CanonicalMakeDepositUsesRealReportAndBaselineForUtilityPrecheck(bool refutation)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        const string gid = "D5/S0/Carrier/Probe";
        var utility = refutation
            ? $"kind=certified-instance; basis=refutes=gid:{gid}.claim; result={gid}.probe; claim={gid}.claim"
            : $"kind=certified-instance; basis=terminal=gid:{gid}.probe";
        var body = refutation
            ? "def claim : Prop := forall n : Nat, n + 1 = n\n"
                + "theorem probe : Not claim := by\n  intro h\n  exact Nat.noConfusion (h 0)\n"
            : "theorem probe : 17 + 4 = 21 := rfl\n";
        var source = TransactionFixture.ExactSixLineLean(TransactionFixture.Gid, body)
            .Replace("   digest:", "   utility: " + utility + "\n   digest:", StringComparison.Ordinal);
        File.WriteAllText(Path.Combine(root, TransactionFixture.LeanPath), source);
        foreach (var path in new[] { "Meta/registry.yaml", "Meta/domains.yaml" })
            File.Copy(Path.Combine(repository, path), Path.Combine(root, path));
        File.Copy(Path.Combine(repository, "lean-toolchain"), Path.Combine(root, "lean-toolchain"));
        File.WriteAllText(Path.Combine(root, "lakefile.toml"),
            "name = \"utility_deposit_fixture\"\ndefaultTargets = [\"D5\"]\n[[lean_lib]]\nname = \"D5\"\nglobs = [\"D5.+\"]\n");
        RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        var cli = Path.Combine(AppContext.BaseDirectory, "StrataLint");
        var obligations = Path.Combine(root, ".lake", "utility-input.json");
        File.WriteAllBytes(obligations, RequireSuccess(TestProcessRunner.Run(cli, ["lean-utility-input"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024)).StandardOutput);
        var report = Path.Combine(root, ".lake", "build", "stratalint", "raw-lean-report.json");
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--run", Path.Combine(repository, "tools/lean-inspector/Inspector.lean"),
            "--output", report + ".spool", "--material-spool", report + ".materials",
            "--utility-input", obligations, "D5.S0.Carrier.Probe", TransactionFixture.LeanPath,
            "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source)))], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        RequireSuccess(TestProcessRunner.Run("python3", [Path.Combine(repository, "tools/lean-inspector/materials.py"), "compact",
            report + ".spool", report + ".materials", report], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));

        // Only surrounding build/emission steps are bounded doubles; the judged precheck is the real CLI.
        WriteExecutable(root, "make", """
            #!/usr/bin/env bash
            case "$1" in
              lean-report) test -s .lake/build/stratalint/raw-lean-report.json ;;
              emit) echo REACHED_EMISSION; exit 77 ;;
              *) exit 96 ;;
            esac
            """);
        WriteExecutable(root, "dotnet", """
            #!/usr/bin/env bash
            while [[ $# -gt 0 && "$1" != -- ]]; do shift; done
            shift
            exec "$UTILITY_TEST_CLI" "$@"
            """);
        var baseline = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("git", ["rev-parse", "HEAD"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024)).StandardOutput).Trim();
        var result = TestProcessRunner.Run("env", [
            "PATH=" + Path.Combine(root, "bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            "UTILITY_TEST_CLI=" + cli,
            "PLAYBOOK_TEST_CALLS=" + Path.Combine(root, "calls"),
            "PLAYBOOK_TEST_FREEZE_PROBES=" + Path.Combine(root, "freeze-probes"),
            "STRATALINT_LEAN_REPORT=" + report,
            "/usr/bin/make", "deposit", "BASE=" + baseline,
            "ATOM_ID=" + TransactionFixture.AtomId, "GID=" + TransactionFixture.Gid,
        ], root, TestBudgets.LeanProcessHangGuard, 1024 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.Equal(2, result.ExitCode);
        if (refutation)
        {
            Assert.Contains("DEPOSIT_HEADER_CHECKED", output, StringComparison.Ordinal);
            Assert.Contains("REACHED_EMISSION", output, StringComparison.Ordinal);
        }
        else
        {
            Assert.Contains("DEPOSIT_HEADER_UTILITY_ORDINARY_INSTANCE_BANNED", output, StringComparison.Ordinal);
            Assert.DoesNotContain("REACHED_EMISSION", output, StringComparison.Ordinal);
        }
        Assert.Equal(0, fixture.FreezeCount());
    }

    private static ProcessOutput RequireSuccess(ProcessOutput result)
    {
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        return result;
    }

    private static void WriteExecutable(string root, string name, string script)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        var path = Path.Combine(root, "bin", name);
        File.WriteAllText(path, script + "\n");
        File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
