using System.Diagnostics;
using System.Globalization;
using System.Runtime.InteropServices;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

// Opt-in boundary observation; never participates in selection or identity.
internal static class AffectedEnvironmentObservation
{
    internal static void Write(string root, string boundary, TestInputManifest? plan = null,
        string? candidate = null, IDictionary<string, string?>? launched = null)
    {
        var destination = Environment.GetEnvironmentVariable("AFFECTED_EVIDENCE_ROOT");
        if (string.IsNullOrEmpty(destination)) return;
        if (plan is null && File.Exists(Path.Combine(root, AffectedTestPlan.PathName)))
            plan = CommonExecutionEvidence.Read<TestInputManifest>(root, AffectedTestPlan.PathName);
        if (candidate is null && File.Exists(Path.Combine(root, CommonExecutionEvidence.BuildPath)))
            candidate = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.BuildPath).Candidate;
        var environment = new ProcessStartInfo().Environment;
        CommonStages.NormalizeEnvironment(environment);
        var child = CommonStages.TestEnvironment();
        var row = new
        {
            boundary, pid = Environment.ProcessId, root,
            expected = plan is null ? null : new { plan.Candidate,
                producer = plan.Actions.Select(action => action.Producer).Distinct().ToArray(),
                environment = plan.Actions.Select(action => action.Environment).Distinct().ToArray() },
            actual = new { candidate, producer = AffectedTestPlan.ProducerIdentity(), environment = child.Identity,
                culture = child.Culture, ui_culture = child.UICulture },
            culture = CultureInfo.CurrentCulture.Name, ui_culture = CultureInfo.CurrentUICulture.Name,
            runtime = RuntimeInformation.RuntimeIdentifier, framework = RuntimeInformation.FrameworkDescription,
            inputs = new[] { "CI", "LANG", "LC_ALL", "LC_CTYPE", "LC_MESSAGES", "DOTNET_CLI_UI_LANGUAGE",
                "VSLANG", "DOTNET_SYSTEM_GLOBALIZATION_INVARIANT", "DOTNET_SYSTEM_GLOBALIZATION_USENLS" }
                .ToDictionary(key => key, Environment.GetEnvironmentVariable),
            normalized = Fingerprints(environment), launch = launched is null ? null : Fingerprints(launched),
        };
        var directory = Path.Combine(destination, Path.GetFileName(root));
        Directory.CreateDirectory(directory);
        File.AppendAllText(Path.Combine(directory, $"identity-{Environment.ProcessId}.jsonl"), JsonSerializer.Serialize(row) + "\n");
    }

    private static Dictionary<string, string> Fingerprints(IDictionary<string, string?> environment) => environment
        .Where(entry => entry.Key.StartsWith("DOTNET_", StringComparison.Ordinal)
            || entry.Key.StartsWith("COMPlus_", StringComparison.Ordinal) || entry.Key.StartsWith("VSTEST_", StringComparison.Ordinal))
        .OrderBy(entry => entry.Key, StringComparer.Ordinal)
        .ToDictionary(entry => entry.Key, entry => AffectedTestPlan.Digest([entry.Value ?? ""]));
}
