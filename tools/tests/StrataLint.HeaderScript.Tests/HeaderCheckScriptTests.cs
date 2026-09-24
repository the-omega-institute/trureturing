using System.Text;
using StrataLint.TestSupport;
using Xunit;
using FactAttribute = Xunit.SkippableFactAttribute;
using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.HeaderScript.Tests;

public sealed class HeaderCheckScriptTests
{
    [Fact]
    public void HeaderCheckScriptRejectsUtilityWithoutSpaceAfterColon()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        var initialize = EngineeringProcess.Capture(repository.Path, "git", ["init", "--quiet", repository.Path],
            hangGuard: TestBudgets.ReportSupervisorHangGuard, maximumOutputBytes: 4096);
        Assert.Equal(0, initialize.Exit);
        var moduleDirectory = Path.Combine(repository.Path, "D5", "S0", "Carrier");
        Directory.CreateDirectory(moduleDirectory);
        var modulePath = Path.Combine(moduleDirectory, "Probe.lean");
        File.WriteAllText(
            modulePath,
            """
            /- GID: D5/S0/Carrier/Probe
               generality: G
               mirror-B: D5/B/S0/Carrier/Probe
               mirror-E: none(waiver:pure-definition)
               anchors: []
               utility:none
               digest: Synthetic fixture. -/
            def probe : Nat := 0
            """ + "\n",
            new UTF8Encoding(false));
        var script = Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "scripts", "agent", "header-check.sh");

        var result = EngineeringProcess.Capture(repository.Path, "/bin/bash", [script, modulePath],
            hangGuard: TestBudgets.ReportSupervisorHangGuard, maximumOutputBytes: 64 * 1024);

        Assert.Equal(1, result.Exit);
        Assert.Contains(
            "第 6 行必须是 '   utility: '",
            result.StandardOutput,
            StringComparison.Ordinal);
    }

    [Fact]
    public void HeaderCheckScriptAcceptsObserved877LineModuleUnderCurrentOwnerLimit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new HeaderCheckScriptFixture();
        fixture.WriteModule(877, finalNewline: true);

        var result = fixture.Run();

        Assert.True(result.Exit == 0, fixture.Diagnostics(result));
        Assert.Contains("(877 行", fixture.StandardOutput(result), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(0, false, 0)]
    [InlineData(0, true, 0)]
    [InlineData(1, false, 1)]
    [InlineData(1, true, 1)]
    public void HeaderCheckScriptUsesStrictOwnerLimitBoundary(
        int excessLines,
        bool finalNewline,
        int expectedExitCode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new HeaderCheckScriptFixture();
        fixture.WriteOwnerLimit(12);
        fixture.WriteModule(12 + excessLines, finalNewline);

        var result = fixture.Run();

        Assert.Equal(expectedExitCode, result.Exit);
        Assert.Contains($"{12 + excessLines} 行", fixture.StandardOutput(result), StringComparison.Ordinal);
    }

    [Fact]
    public void HeaderCheckScriptOwnerLimitChangeAloneChangesVerdict()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new HeaderCheckScriptFixture();
        fixture.WriteModule(10, finalNewline: true);
        fixture.WriteOwnerLimit(10);

        var atLimit = fixture.Run();
        fixture.WriteOwnerLimit(9);
        var aboveLimit = fixture.Run();

        Assert.True(atLimit.Exit == 0, fixture.Diagnostics(atLimit));
        Assert.Equal(1, aboveLimit.Exit);
        Assert.Contains("超 SL-003 硬线 9", fixture.StandardOutput(aboveLimit), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("unreadable")]
    [InlineData("malformed")]
    [InlineData("duplicate")]
    public void HeaderCheckScriptFailsClosedWhenArtifactLimitOwnerIsUnavailableOrAmbiguous(string fault)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new HeaderCheckScriptFixture();
        fixture.WriteModule(8, finalNewline: true);
        fixture.FaultOwner(fault);

        var result = fixture.Run();

        Assert.Equal(1, result.Exit);
        Assert.Contains(
            "无法从", fixture.StandardOutput(result), StringComparison.Ordinal);
        Assert.Contains(
            "ArtifactHardLineLimit", fixture.StandardOutput(result), StringComparison.Ordinal);
    }

    [Fact]
    public void HeaderCheckScriptCountsOnlyLfWhenSourceContainsInternalCarriageReturn()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new HeaderCheckScriptFixture();
        fixture.WriteOwnerLimit(8);
        fixture.WriteModule(8, finalNewline: true, internalCarriageReturn: true);

        var result = fixture.Run();

        Assert.True(result.Exit == 0, fixture.Diagnostics(result));
        Assert.Contains("(8 行", fixture.StandardOutput(result), StringComparison.Ordinal);
    }

    private sealed class HeaderCheckScriptFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();

        internal HeaderCheckScriptFixture()
        {
            var sourceRoot = TestRepositoryLayout.FindRoot();
            ScriptPath = Path.Combine(repository.Path, "tools", "scripts", "agent", "header-check.sh");
            OwnerPath = Path.Combine(
                repository.Path,
                "tools", "StrataLint.Engine", "Rules", "RepositoryRules.Structure.cs");
            ModulePath = Path.Combine(repository.Path, "D5", "S0", "Carrier", "Probe.lean");
            Directory.CreateDirectory(Path.GetDirectoryName(ScriptPath)!);
            Directory.CreateDirectory(Path.GetDirectoryName(OwnerPath)!);
            Directory.CreateDirectory(Path.GetDirectoryName(ModulePath)!);
            File.Copy(
                Path.Combine(sourceRoot, "tools", "scripts", "agent", "header-check.sh"),
                ScriptPath);
            File.Copy(
                Path.Combine(
                    sourceRoot,
                    "tools", "StrataLint.Engine", "Rules", "RepositoryRules.Structure.cs"),
                OwnerPath);
            var initialize = EngineeringProcess.Capture(repository.Path, "git", ["init", "--quiet", repository.Path],
                hangGuard: TestBudgets.ReportSupervisorHangGuard, maximumOutputBytes: 4096);
            Assert.Equal(0, initialize.Exit);
        }

        private string ScriptPath { get; }

        private string OwnerPath { get; }

        private string ModulePath { get; }

        internal void WriteOwnerLimit(int limit) =>
            File.WriteAllText(
                OwnerPath,
                $$"""
                internal static partial class RepositoryRules
                {
                    internal const int ArtifactHardLineLimit = {{limit}};
                    internal const int DirectoryFileLimit = 96;
                }
                """ + "\n",
                new UTF8Encoding(false));

        internal void WriteModule(
            int lineCount,
            bool finalNewline,
            bool internalCarriageReturn = false)
        {
            Assert.True(lineCount >= 7);
            var lines = new List<string>
            {
                "/- GID: D5/S0/Carrier/Probe",
                "   generality: I",
                "   mirror-B: D5/B/S0/Carrier/Probe",
                "   mirror-E: none(waiver:synthetic-fixture)",
                "   anchors: []",
                "   digest: Synthetic fixture. -/",
            };
            lines.AddRange(Enumerable.Range(1, lineCount - lines.Count).Select(index => $"-- filler {index}"));
            if (internalCarriageReturn)
            {
                lines[6] = "-- left\rright";
            }

            var text = string.Join('\n', lines) + (finalNewline ? "\n" : string.Empty);
            File.WriteAllText(ModulePath, text, new UTF8Encoding(false));
        }

        internal void FaultOwner(string fault)
        {
            switch (fault)
            {
                case "missing":
                    File.Delete(OwnerPath);
                    break;
                case "unreadable":
                    if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
                    File.SetUnixFileMode(OwnerPath, UnixFileMode.None);
                    break;
                case "malformed":
                    File.WriteAllText(
                        OwnerPath,
                        "internal const int ArtifactHardLineLimit = invalid;\n"
                            + "internal const int DirectoryFileLimit = 96;\n",
                        new UTF8Encoding(false));
                    break;
                case "duplicate":
                    File.WriteAllText(
                        OwnerPath,
                        "internal const int ArtifactHardLineLimit = 8;\n"
                            + "internal const int ArtifactHardLineLimit = 9;\n"
                            + "internal const int DirectoryFileLimit = 96;\n",
                        new UTF8Encoding(false));
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(fault), fault, null);
            }
        }

        internal (int Exit, string StandardOutput, string StandardError) Run() => EngineeringProcess.Capture(repository.Path, "/bin/bash", [ScriptPath, ModulePath],
            hangGuard: TestBudgets.ReportSupervisorHangGuard, maximumOutputBytes: 64 * 1024);

        internal string StandardOutput((int Exit, string StandardOutput, string StandardError) result) =>
            result.StandardOutput;

        internal string Diagnostics((int Exit, string StandardOutput, string StandardError) result) =>
            StandardOutput(result) + result.StandardError;

        public void Dispose() => repository.Dispose();
    }
}
