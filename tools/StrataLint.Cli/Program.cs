using StrataLint.Engine;

namespace StrataLint.Cli;

public static class Program
{
    public static int Main(string[] args)
    {
        MaintenanceLogAdapter.Start();
        var exitCode = CliApplication.Run(
            args,
            new ProductionCliEnvironment(Environment.CurrentDirectory),
            new SystemCliConsole());
        MaintenanceLogAdapter.Finish(exitCode);
        return exitCode;
    }
}
