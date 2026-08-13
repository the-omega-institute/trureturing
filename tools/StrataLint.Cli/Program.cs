namespace StrataLint.Cli;

public static class Program
{
    public static int Main(string[] args) => CliApplication.Run(
        args,
        new ProductionCliEnvironment(Environment.CurrentDirectory),
        new SystemCliConsole());
}
