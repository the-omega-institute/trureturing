using StrataLint.Engine;

namespace StrataLint.Cli;

public static class Program
{
    public static int Main(string[] args)
    {
        var entry = TimeProvider.System.GetTimestamp();
        DefaultCliStartupProbe.EnterChild(entry);
        var probe = DefaultCliStartupProbe.Current.Value;
        try
        {
            probe?.Mark("environment-begin");
            var environment = new ProductionCliEnvironment(Environment.CurrentDirectory);
            probe?.Mark("environment-end");
            probe?.Resources("environment-end");
            probe?.Mark("command-begin");
            var result = CliApplication.Run(args, environment, new SystemCliConsole());
            probe?.Mark("command-end", new { exit_code = result });
            return result;
        }
        finally
        {
            probe?.Complete();
            DefaultCliStartupProbe.Current.Value = null;
        }
    }
}
