using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerFrozenCommandTests
{
    [Fact]
    public void ActiveFreezeReturnsZeroOnTheAllowSide()
    {
        using var fixture = new Fixture(createLedgerDirectory: true);
        fixture.WriteActiveFreeze();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void MissingActiveFreezeReturnsOne()
    {
        using var fixture = new Fixture(createLedgerDirectory: true);

        var result = fixture.Run();

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void MissingLedgerDirectoryReturnsTwoAsInfrastructureFailure()
    {
        using var fixture = new Fixture(createLedgerDirectory: false);

        var result = fixture.Run();

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains(
            "LEDGER_FROZEN_INVALID frozen ledger is missing: Golden/Frozen/accepted",
            result.Error,
            StringComparison.Ordinal);
    }

    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal Fixture(bool createLedgerDirectory)
        {
            Git("init", "-q");
            if (createLedgerDirectory)
            {
                Directory.CreateDirectory(AcceptedDirectory);
            }
        }

        private string AcceptedDirectory => Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                '/',
                Path.DirectorySeparatorChar));

        internal void WriteActiveFreeze() =>
            WriteLedgerDirectory(AcceptedDirectory, EventFiles(BuildCatalog(Module("A"))));

        internal (int ExitCode, string Output, string Error) Run()
        {
            var console = new BufferedConsole();
            var exitCode = CliApplication.Run(
                ["ledger-frozen", "--target", PathFor("A")],
                new ProductionCliEnvironment(temporary.Path),
                console);
            return (exitCode, console.Output, console.Error);
        }

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                temporary.Path,
                TestBudgets.LocalProcessHangGuard,
                128 * 1024);
            Assert.Equal(0, result.ExitCode);
        }

        public void Dispose() => temporary.Dispose();
    }
}
