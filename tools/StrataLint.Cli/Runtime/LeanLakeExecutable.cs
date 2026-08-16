namespace StrataLint.Cli;

internal static class LeanLakeExecutable
{
    internal const string OverrideVariable = "LAKE_BIN";

    internal static bool TryResolve(out string executable, out string reason)
    {
        var attempts = new List<string>();
        var configured = Environment.GetEnvironmentVariable(OverrideVariable);
        if (string.IsNullOrWhiteSpace(configured))
        {
            attempts.Add($"{OverrideVariable} is unset");
        }
        else if (TryAbsoluteExecutable(configured, out executable))
        {
            reason = string.Empty;
            return true;
        }
        else
        {
            attempts.Add($"{OverrideVariable}={configured} (not an absolute executable file)");
        }

        var path = Environment.GetEnvironmentVariable("PATH");
        if (string.IsNullOrEmpty(path))
        {
            attempts.Add("PATH is unset or empty");
        }
        else
        {
            foreach (var directory in path.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
            {
                foreach (var name in ExecutableNames())
                {
                    string candidate;
                    try
                    {
                        candidate = Path.GetFullPath(Path.Combine(directory, name));
                    }
                    catch (Exception exception) when (exception is ArgumentException or NotSupportedException)
                    {
                        attempts.Add($"PATH entry {directory} ({exception.Message})");
                        continue;
                    }

                    attempts.Add(candidate);
                    if (IsExecutable(candidate))
                    {
                        executable = candidate;
                        reason = string.Empty;
                        return true;
                    }
                }
            }
        }

        var home = Environment.GetEnvironmentVariable("HOME");
        if (string.IsNullOrWhiteSpace(home))
        {
            attempts.Add("HOME is unset; cannot try $HOME/.elan/bin/lake");
        }
        else
        {
            var candidate = Path.GetFullPath(Path.Combine(home, ".elan", "bin", ExecutableNames()[0]));
            attempts.Add(candidate);
            if (IsExecutable(candidate))
            {
                executable = candidate;
                reason = string.Empty;
                return true;
            }
        }

        executable = string.Empty;
        reason = "lake executable could not be resolved; tried " + string.Join("; ", attempts);
        return false;
    }

    private static bool TryAbsoluteExecutable(string candidate, out string executable)
    {
        if (Path.IsPathFullyQualified(candidate))
        {
            var fullPath = Path.GetFullPath(candidate);
            if (IsExecutable(fullPath))
            {
                executable = fullPath;
                return true;
            }
        }

        executable = string.Empty;
        return false;
    }

    private static string[] ExecutableNames() =>
        OperatingSystem.IsWindows() ? ["lake.exe", "lake"] : ["lake"];

    private static bool IsExecutable(string path)
    {
        if (!File.Exists(path)) return false;
        if (OperatingSystem.IsWindows()) return true;

        try
        {
            const UnixFileMode executable =
                UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute;
            return (File.GetUnixFileMode(path) & executable) != 0;
        }
        catch (PlatformNotSupportedException)
        {
            return false;
        }
    }
}
