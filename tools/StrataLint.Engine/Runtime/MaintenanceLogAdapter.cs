using System.Diagnostics;
using System.Globalization;
using System.Text.Json;

namespace StrataLint.Engine;

/// <summary>Records observations without supervising the business command.</summary>
public static class MaintenanceLogAdapter
{
    private static string? source;
    private static string? state;
    private static Dictionary<string, object?> lastFields = new();
    private static string executable = "python3";

    public static void Start()
    {
        var script = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_SCRIPT");
        var repository = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_REPOSITORY");
        if (string.IsNullOrEmpty(script) || string.IsNullOrEmpty(repository)
            || !string.IsNullOrEmpty(Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_RUN_ID"))) return;
        try
        {
            source = File.ReadAllText(Path.Combine(repository, "tools", "scripts", "maintenance_log.py"));
            var result = Observe("begin", "--script", script, "--repository", repository,
                "--owner-pid", Environment.ProcessId.ToString(CultureInfo.InvariantCulture));
            var separator = result.IndexOf(':');
            if (separator == 32 && result[..separator].All(char.IsAsciiHexDigit))
            {
                using var payload = JsonDocument.Parse(Convert.FromBase64String(result[(separator + 1)..]));
                var resolved = payload.RootElement.GetProperty("interpreter").GetString();
                if (string.IsNullOrEmpty(resolved) || !Path.IsPathFullyQualified(resolved)) return;
                executable = resolved;
                state = result;
                Environment.SetEnvironmentVariable("TRURETURING_MAINTENANCE_RUN_ID", result[..separator]);
            }
        }
        catch
        {
            // Observation failure cannot change the native command result.
        }
    }

    public static void Finish(int exitCode)
    {
        if (state is null) return;
        try
        {
            _ = Observe("finish", "--state", state, "--exit-code", exitCode.ToString(CultureInfo.InvariantCulture),
                "--fields", JsonSerializer.Serialize(lastFields));
        }
        catch
        {
            // Source and cwd may already have been removed; the writer is loaded.
        }
    }

    public static void Record(string operation, string? status, string? stage,
        string? reasonCode, string? errorType, IReadOnlyDictionary<string, object?>? details = null)
    {
        if (state is null || string.IsNullOrWhiteSpace(operation)) return;
        try
        {
            var fields = new Dictionary<string, object?>
            {
                ["action"] = operation,
                ["operation"] = operation,
                ["status"] = status,
                ["outcome"] = status,
                ["stage"] = stage,
                ["reason_code"] = reasonCode,
                ["error_type"] = errorType,
            };
            if (details is not null)
            {
                foreach (var (key, value) in details)
                    if (key is not ("action" or "operation" or "status" or "outcome" or "stage"
                        or "reason_code" or "error_type"))
                        fields[key] = value;
            }

            lastFields = fields;
            _ = Observe("emit", "--state", state, "--event", "operation_finished",
                "--fields", JsonSerializer.Serialize(fields));
        }
        catch
        {
            // Observation failure cannot change the native command result.
        }
    }

    private static string Observe(params string[] arguments)
    {
        using var process = new Process
        {
            StartInfo = new ProcessStartInfo
            {
                FileName = executable,
                WorkingDirectory = Path.GetPathRoot(Path.GetTempPath())!,
                UseShellExecute = false,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            },
        };
        process.StartInfo.ArgumentList.Add("-B");
        process.StartInfo.ArgumentList.Add("-c");
        process.StartInfo.ArgumentList.Add(source!);
        foreach (var argument in arguments) process.StartInfo.ArgumentList.Add(argument);
        process.Start();
        process.StandardInput.Close();
        var output = process.StandardOutput.ReadToEndAsync();
        var error = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        _ = error.GetAwaiter().GetResult();
        return process.ExitCode == 0 ? output.GetAwaiter().GetResult().Trim() : "";
    }
}
