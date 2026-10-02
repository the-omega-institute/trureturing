using System.Globalization;
using System.Runtime.InteropServices;

namespace StrataLint.Scribe;

public sealed record ScribeResourcePackExecutionEnvironment
{
    public ScribeResourcePackExecutionEnvironment(string dotnetRuntimeVersion, string globalizationBackend,
        string globalizationBackendDataVersion)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(dotnetRuntimeVersion);
        ArgumentException.ThrowIfNullOrWhiteSpace(globalizationBackend);
        ArgumentException.ThrowIfNullOrWhiteSpace(globalizationBackendDataVersion);
        DotnetRuntimeVersion = dotnetRuntimeVersion;
        GlobalizationBackend = globalizationBackend;
        GlobalizationBackendDataVersion = globalizationBackendDataVersion;
    }

    public string DotnetRuntimeVersion { get; init; }
    public string GlobalizationBackend { get; init; }
    public string GlobalizationBackendDataVersion { get; init; }

    public static ScribeResourcePackExecutionEnvironment Current => new(
        Environment.Version.ToString(),
        CurrentGlobalizationBackend(),
        CurrentBackendDataVersion());

    internal IEnumerable<string> Differences(ScribeResourcePackExecutionEnvironment other)
    {
        if (!string.Equals(DotnetRuntimeVersion, other.DotnetRuntimeVersion, StringComparison.Ordinal))
            yield return "dotnetRuntimeVersion";
        if (!string.Equals(GlobalizationBackend, other.GlobalizationBackend, StringComparison.Ordinal))
            yield return "globalizationBackend";
        if (!string.Equals(GlobalizationBackendDataVersion, other.GlobalizationBackendDataVersion, StringComparison.Ordinal))
            yield return "globalizationBackendDataVersion";
    }

    private static string CurrentBackendDataVersion()
    {
        var version = CultureInfo.InvariantCulture.CompareInfo.Version;
        return version.FullVersion.ToString(CultureInfo.InvariantCulture) + ":" + version.SortId.ToString("D");
    }

    private static string CurrentGlobalizationBackend()
    {
        if (AppContext.TryGetSwitch("System.Globalization.Invariant", out var invariant) && invariant)
            return "invariant";
        return RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "nls" : "icu";
    }
}
