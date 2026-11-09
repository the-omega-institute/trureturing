using StrataLint.Engine;
using System.Runtime.InteropServices;

namespace StrataLint.EngineeringScope;

internal static class LeanProgram
{
    public static int Main(string[] arguments)
    {
        MaintenanceLogAdapter.Start();
        var exitCode = 2;
        try
        {
            if (arguments.FirstOrDefault() == "lean-utility-input")
            {
                var result = LeanUtilityInputCommand.Run(
                    Directory.GetCurrentDirectory(), arguments.Skip(1).ToArray());
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                exitCode = result.ExitCode;
            }
            else if (arguments.FirstOrDefault() is "ensure-cache" or "with-cache-reader" or "with-cache-writer")
            {
                var root = Directory.GetCurrentDirectory();
                var rest = arguments.Skip(1).ToArray();
                exitCode = RunCache(root, rest, arguments[0] != "ensure-cache");
            }
            else throw new ArgumentException("expected lean-utility-input, ensure-cache, with-cache-reader or with-cache-writer");
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"LEAN_PRODUCER_FAILED {exception.Message}");
            exitCode = 2;
        }
        MaintenanceLogAdapter.Finish(exitCode);
        return exitCode;
    }

    private static int RunCache(string root, string[] arguments, bool wrapped)
    {
        using var cancellation = new CancellationTokenSource();
        var signalExit = 0;
        void Cancel(PosixSignalContext context)
        {
            context.Cancel = true;
            Interlocked.CompareExchange(ref signalExit, context.Signal == PosixSignal.SIGINT ? 130 : 143, 0);
            cancellation.Cancel();
        }
        using var term = OperatingSystem.IsWindows() ? null : PosixSignalRegistration.Create(PosixSignal.SIGTERM, Cancel);
        using var interrupt = OperatingSystem.IsWindows() ? null : PosixSignalRegistration.Create(PosixSignal.SIGINT, Cancel);
        using var stdout = Console.OpenStandardOutput();
        using var stderr = Console.OpenStandardError();
        var observation = LeanCacheCommandObservation.FromEnvironment();
        var phase = wrapped ? "cache-reader" : "cache-ensure";
        var exit = 2;
        observation?.Boundary(phase, "start");
        try
        {
            var runner = new ProductionWorktreeProcessRunner(cancellation.Token, observation);
            var result = wrapped
                ? LeanCacheEnsureCommand.RunWithWriter(root, arguments, runner, new ApfsDirectoryCloner(),
                    standardOutput: observation?.Output(stdout) ?? stdout,
                    standardError: observation?.Error(stderr) ?? stderr)
                : LeanCacheEnsureCommand.Run(root, arguments, runner, new ApfsDirectoryCloner(),
                    continueOnCacheGetFailure: true);
            Console.Out.Write(result.Output);
            Console.Error.Write(result.Error);
            exit = signalExit != 0 ? signalExit : result.ExitCode ?? (result.Success ? 0 : 2);
            return exit;
        }
        catch (OperationCanceledException) when (cancellation.IsCancellationRequested)
        {
            exit = signalExit != 0 ? signalExit : 2;
            return exit;
        }
        finally
        {
            if (signalExit != 0)
            {
                exit = signalExit;
                Console.Error.WriteLine($"LEAN_CACHE_INTERRUPTED exit={exit}");
                MaintenanceLogAdapter.Record(wrapped ? "cache-reader" : "ensure-cache",
                    "interrupted", phase, "signal", null);
            }
            observation?.Boundary(phase, "finish", rawExit: exit);
        }
    }
}
