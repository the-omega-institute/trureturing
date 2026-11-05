using StrataLint.Engine;
using System.Text.Json;
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
                if (arguments[0] is "with-cache-reader" or "with-cache-writer")
                    exitCode = RunReader(root, rest);
                else
                {
                    var runner = new ProductionWorktreeProcessRunner();
                    // This leaf prepares subsequent Lean work. Optional binary-cache
                    // transfer failures leave the normal build responsible for success.
                    var result = LeanCacheEnsureCommand.Run(root, rest, runner, new ApfsDirectoryCloner(),
                        continueOnCacheGetFailure: true);
                    exitCode = result.ExitCode ?? (result.Success ? 0 : 2);
                    RecordEnsureObservation(result, exitCode);
                    Console.Out.Write(result.Output);
                    Console.Error.Write(result.Error);
                }
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

    private static void RecordEnsureObservation(CommandResult result, int exitCode)
    {
        const string prefix = "LEAN_CACHE ";
        var line = result.Output.Split('\n').FirstOrDefault(value =>
            value.StartsWith(prefix, StringComparison.Ordinal));
        if (line is null)
        {
            MaintenanceLogAdapter.Record("ensure-cache", exitCode == 0 ? "succeeded" : "failed",
                "result", null, exitCode == 0 ? null : "CommandResult");
            return;
        }

        try
        {
            using var document = JsonDocument.Parse(line[prefix.Length..]);
            var payload = document.RootElement;
            string? Text(string name) =>
                payload.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
                    ? value.GetString() : null;
            var status = Text("status") ?? (exitCode == 0 ? "succeeded" : "failed");
            var reason = Text("reason") ?? Text("archive_reason");
            var details = new Dictionary<string, object?>();
            foreach (var name in new[]
            {
                "method", "archive_status", "archive_mode", "archive_skip_reason",
                "project_olean_state", "mathlib_olean_state", "stamp_miss", "cold_build_consent"
            })
                if (payload.TryGetProperty(name, out var value)
                    && value.ValueKind is JsonValueKind.String or JsonValueKind.True or JsonValueKind.False)
                    details[name] = value.Clone();
            MaintenanceLogAdapter.Record("ensure-cache", status, "result",
                BoundedCode(reason), exitCode == 0 ? null : status == "refused" ? "Refused" : "CommandResult",
                details);
        }
        catch (JsonException)
        {
            MaintenanceLogAdapter.Record("ensure-cache", exitCode == 0 ? "succeeded" : "failed",
                "result", "malformed_receipt", "JsonException");
        }
    }

    private static string? BoundedCode(string? value)
    {
        if (string.IsNullOrWhiteSpace(value)) return null;
        var code = value.Trim().Split(':', ' ', StringSplitOptions.RemoveEmptyEntries)[0];
        var filtered = new string(code.Where(character => char.IsAsciiLetterOrDigit(character)
            || character is '_' or '-' or '.').ToArray());
        return filtered.Length == 0 ? "unknown" : filtered[..Math.Min(96, filtered.Length)];
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
        var observation = LeanCacheCommandObservation.FromEnvironment();
        observation?.Boundary("cache-reader", "start");
        try
        {
            var result = LeanCacheEnsureCommand.RunWithWriter(root, arguments,
                new ProductionWorktreeProcessRunner(cancellation.Token, observation), new ApfsDirectoryCloner(),
                standardOutput: observation?.Output(stdout) ?? stdout,
                standardError: observation?.Error(stderr) ?? stderr);
            Console.Out.Write(result.Output);
            Console.Error.Write(result.Error);
            var exit = signalExit != 0 ? signalExit : result.ExitCode ?? (result.Success ? 0 : 2);
            observation?.Boundary("cache-reader", "finish", rawExit: exit);
            return exit;
        }
        catch (OperationCanceledException) when (cancellation.IsCancellationRequested)
        {
            return signalExit != 0 ? signalExit : 2;
        }
    }
}
