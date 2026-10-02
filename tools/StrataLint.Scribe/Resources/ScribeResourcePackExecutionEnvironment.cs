using System.Runtime.InteropServices;

namespace StrataLint.Scribe;

public sealed record ScribeResourcePackExecutionEnvironment
{
    public ScribeResourcePackExecutionEnvironment(string dotnetRuntimeVersion, string globalizationBackend)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(dotnetRuntimeVersion);
        ArgumentException.ThrowIfNullOrWhiteSpace(globalizationBackend);
        DotnetRuntimeVersion = dotnetRuntimeVersion;
        GlobalizationBackend = globalizationBackend;
    }

    public string DotnetRuntimeVersion { get; init; }
    public string GlobalizationBackend { get; init; }

    public static ScribeResourcePackExecutionEnvironment Current => new(
        Environment.Version.ToString(),
        CurrentGlobalizationBackend());

    internal IEnumerable<string> Differences(ScribeResourcePackExecutionEnvironment other)
    {
        if (!string.Equals(DotnetRuntimeVersion, other.DotnetRuntimeVersion, StringComparison.Ordinal))
            yield return "dotnetRuntimeVersion";
        if (!string.Equals(GlobalizationBackend, other.GlobalizationBackend, StringComparison.Ordinal))
            yield return "globalizationBackend";
    }

    private static string CurrentGlobalizationBackend()
    {
        if (AppContext.TryGetSwitch("System.Globalization.Invariant", out var invariant) && invariant)
            return "invariant";
        return RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "nls" : "icu";
    }
}
