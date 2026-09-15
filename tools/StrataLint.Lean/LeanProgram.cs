using StrataLint.Engine;
using System.Runtime.InteropServices;

namespace StrataLint.EngineeringScope;

internal static class LeanProgram
{
    public static int Main(string[] arguments)
    {
        try
        {
            if (arguments.FirstOrDefault() == "lean-utility-input")
            {
                var result = LeanUtilityInputCommand.Run(
                    () => GitRepositorySnapshotReader.ReadCurrent(Directory.GetCurrentDirectory()), arguments.Skip(1).ToArray());
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                return result.ExitCode;
            }
            if (arguments.FirstOrDefault() is "ensure-cache" or "with-cache-reader" or "with-cache-writer")
            {
                var root = Directory.GetCurrentDirectory();
                var rest = arguments.Skip(1).ToArray();
                if (arguments[0] is "with-cache-reader" or "with-cache-writer") return RunReader(root, rest);
                var runner = new ProductionWorktreeProcessRunner();
                var result = LeanCacheEnsureCommand.Run(root, rest, runner, new ApfsDirectoryCloner());
                Console.Out.Write(result.Output);
                Console.Error.Write(result.Error);
                return result.ExitCode ?? (result.Success ? 0 : 2);
            }
            throw new ArgumentException("expected lean-utility-input, ensure-cache, with-cache-reader or with-cache-writer");
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"LEAN_PRODUCER_FAILED {exception.Message}");
            return 2;
        }
    }

    private static int RunReader(string root, string[] arguments)
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
        try
        {
            var result = LeanCacheEnsureCommand.RunWithWriter(root, arguments,
                new ProductionWorktreeProcessRunner(cancellation.Token), new ApfsDirectoryCloner(),
                standardOutput: stdout, standardError: stderr);
            Console.Out.Write(result.Output);
            Console.Error.Write(result.Error);
            return signalExit != 0 ? signalExit : result.ExitCode ?? (result.Success ? 0 : 2);
        }
        catch (OperationCanceledException) when (cancellation.IsCancellationRequested)
        {
            return signalExit != 0 ? signalExit : 2;
        }
    }
}
