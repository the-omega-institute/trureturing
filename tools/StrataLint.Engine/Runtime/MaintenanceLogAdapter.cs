using System.Diagnostics;
using System.Globalization;

namespace StrataLint.Engine;

/// <summary>
/// Best-effort completion adapter for native owners whose lifecycle starts in
/// a shell entrypoint. It never starts or supervises the business command.
/// </summary>
public static class MaintenanceLogAdapter
{
    public static void Start()
    {
        var script = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_SCRIPT");
        var repository = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_REPOSITORY");
        if (string.IsNullOrEmpty(script) || string.IsNullOrEmpty(repository)
            || !string.IsNullOrEmpty(Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_RUN_ID"))) return;

        var helper = Path.Combine(repository, "tools", "scripts", "maintenance_log.py");
        if (!File.Exists(helper)) return;
        try
        {
            using var process = CreateProcess(helper, "begin", script, repository);
            process.StartInfo.ArgumentList.Add("--owner-pid");
            process.StartInfo.ArgumentList.Add(Environment.ProcessId.ToString(CultureInfo.InvariantCulture));
            if (!process.Start()) return;
            process.StandardInput.Close();
            var runId = process.StandardOutput.ReadToEnd().Trim();
            _ = process.StandardError.ReadToEnd();
            process.WaitForExit();
            if (process.ExitCode == 0 && runId.Length == 32
                && runId.All(static character => char.IsAsciiHexDigit(character)))
                Environment.SetEnvironmentVariable("TRURETURING_MAINTENANCE_RUN_ID", runId);
        }
        catch
        {
            // Maintenance logging is observation only and cannot change the command result.
        }
    }

    public static void Finish(int exitCode)
    {
        var script = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_SCRIPT");
        var repository = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_REPOSITORY");
        var runId = Environment.GetEnvironmentVariable("TRURETURING_MAINTENANCE_RUN_ID");
        if (string.IsNullOrEmpty(script) || string.IsNullOrEmpty(repository) || string.IsNullOrEmpty(runId)) return;

        var helper = Path.Combine(repository, "tools", "scripts", "maintenance_log.py");
        if (!File.Exists(helper)) return;

        try
        {
            using var process = CreateProcess(helper, "finish", script, repository);
            process.StartInfo.ArgumentList.Add("--run-id");
            process.StartInfo.ArgumentList.Add(runId);
            process.StartInfo.ArgumentList.Add("--owner-pid");
            process.StartInfo.ArgumentList.Add(Environment.ProcessId.ToString(CultureInfo.InvariantCulture));
            process.StartInfo.ArgumentList.Add("--exit-code");
            process.StartInfo.ArgumentList.Add(exitCode.ToString(CultureInfo.InvariantCulture));
            if (!process.Start()) return;
            process.StandardInput.Close();
            process.WaitForExit();
            _ = process.StandardOutput.ReadToEnd();
            _ = process.StandardError.ReadToEnd();
        }
        catch
        {
            // Maintenance logging is observation only and cannot change the command result.
        }
    }

    private static Process CreateProcess(string helper, string action, string script, string repository)
    {
        var process = new Process
        {
            StartInfo = new ProcessStartInfo
            {
                FileName = "python3",
                UseShellExecute = false,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            },
        };
        process.StartInfo.ArgumentList.Add("-B");
        process.StartInfo.ArgumentList.Add(helper);
        process.StartInfo.ArgumentList.Add(action);
        process.StartInfo.ArgumentList.Add("--script");
        process.StartInfo.ArgumentList.Add(script);
        process.StartInfo.ArgumentList.Add("--repository");
        process.StartInfo.ArgumentList.Add(repository);
        return process;
    }
}
