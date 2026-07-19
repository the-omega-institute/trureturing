using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.Json;

namespace StrataLint.Cli;

internal sealed record PerfCohort(
    string Venue,
    string Os,
    string Arch,
    string CpuClass,
    string? RunnerClass);

internal sealed record PerfContext(
    string Commit,
    string Base,
    string WorkloadId,
    string? CacheState,
    double? LoadavgPerCpu,
    int? HostConcurrency);

internal sealed record PerfResources(
    double? DiskFreeGb,
    int? FdPeak,
    double? RssPeakMb);

internal sealed record PerfEvent(
    string Schema,
    string RunId,
    DateTimeOffset Timestamp,
    PerfCohort Cohort,
    PerfContext Context,
    string Kind,
    string Stage,
    string Status,
    double? ElapsedSeconds,
    PerfResources Resources);

internal static class PerfEventCodec
{
    internal const string Schema = "stratalint-perf-event-v1";

    private static readonly ImmutableHashSet<string> Venues =
        ImmutableHashSet.Create(StringComparer.Ordinal, "local", "ci");
    private static readonly ImmutableHashSet<string> Kinds =
        ImmutableHashSet.Create(StringComparer.Ordinal, "timing", "resource");
    private static readonly ImmutableHashSet<string> Statuses =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "passed",
            "failed",
            "skipped",
            "observation");

    internal static PerfEvent ParseLine(string line)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(line);
        using var document = JsonDocument.Parse(line);
        var root = RequireObject(document.RootElement, "event");
        var schema = RequireString(root, "schema", "schema");
        if (!string.Equals(schema, Schema, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"unsupported perf event schema '{schema}'");
        }

        var runId = RequireString(root, "run_id", "run_id");
        var timestampText = RequireString(root, "ts", "ts");
        if (!DateTimeOffset.TryParseExact(
                timestampText,
                "yyyy-MM-dd'T'HH:mm:ss'Z'",
                CultureInfo.InvariantCulture,
                DateTimeStyles.AssumeUniversal | DateTimeStyles.AdjustToUniversal,
                out var timestamp))
        {
            throw new InvalidOperationException("ts must be a UTC second timestamp");
        }

        var cohortElement = RequireObject(RequireProperty(root, "cohort", "cohort"), "cohort");
        var venue = RequireMember(
            Venues,
            RequireString(cohortElement, "venue", "cohort.venue"),
            "cohort.venue");
        var cohort = new PerfCohort(
            venue,
            RequireString(cohortElement, "os", "cohort.os"),
            RequireString(cohortElement, "arch", "cohort.arch"),
            RequireString(cohortElement, "cpu_class", "cohort.cpu_class"),
            OptionalString(cohortElement, "runner_class", "cohort.runner_class"));

        var contextElement = RequireObject(RequireProperty(root, "context", "context"), "context");
        var context = new PerfContext(
            RequireString(contextElement, "commit", "context.commit"),
            RequireString(contextElement, "base", "context.base"),
            RequireString(contextElement, "workload_id", "context.workload_id"),
            OptionalString(contextElement, "cache_state", "context.cache_state"),
            OptionalDouble(contextElement, "loadavg_per_cpu", "context.loadavg_per_cpu"),
            OptionalInt(contextElement, "host_concurrency", "context.host_concurrency"));
        var kind = RequireMember(Kinds, RequireString(root, "kind", "kind"), "kind");
        var stage = RequireString(root, "stage", "stage");
        var status = RequireMember(Statuses, RequireString(root, "status", "status"), "status");
        var elapsed = OptionalDouble(root, "elapsed_seconds", "elapsed_seconds");
        if (elapsed < 0)
        {
            throw new InvalidOperationException("elapsed_seconds cannot be negative");
        }

        var resourcesElement = RequireObject(
            RequireProperty(root, "resources", "resources"),
            "resources");
        var resources = new PerfResources(
            OptionalDouble(resourcesElement, "disk_free_gb", "resources.disk_free_gb"),
            OptionalInt(resourcesElement, "fd_peak", "resources.fd_peak"),
            OptionalDouble(resourcesElement, "rss_peak_mb", "resources.rss_peak_mb"));
        if (resources.DiskFreeGb < 0 || resources.FdPeak < 0 || resources.RssPeakMb < 0)
        {
            throw new InvalidOperationException("resource measurements cannot be negative");
        }

        if (CriticalContextMissing(context)) status = "observation";
        return new PerfEvent(
            schema,
            runId,
            timestamp,
            cohort,
            context,
            kind,
            stage,
            status,
            elapsed,
            resources);
    }

    internal static string WriteLine(PerfEvent item)
    {
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream))
        {
            writer.WriteStartObject();
            writer.WriteString("schema", item.Schema);
            writer.WriteString("run_id", item.RunId);
            writer.WriteString(
                "ts",
                item.Timestamp.ToUniversalTime().ToString(
                    "yyyy-MM-dd'T'HH:mm:ss'Z'",
                    CultureInfo.InvariantCulture));
            writer.WriteStartObject("cohort");
            writer.WriteString("venue", item.Cohort.Venue);
            writer.WriteString("os", item.Cohort.Os);
            writer.WriteString("arch", item.Cohort.Arch);
            writer.WriteString("cpu_class", item.Cohort.CpuClass);
            WriteOptionalString(writer, "runner_class", item.Cohort.RunnerClass);
            writer.WriteEndObject();
            writer.WriteStartObject("context");
            writer.WriteString("commit", item.Context.Commit);
            writer.WriteString("base", item.Context.Base);
            writer.WriteString("workload_id", item.Context.WorkloadId);
            WriteOptionalString(writer, "cache_state", item.Context.CacheState);
            WriteOptionalNumber(writer, "loadavg_per_cpu", item.Context.LoadavgPerCpu);
            WriteOptionalNumber(writer, "host_concurrency", item.Context.HostConcurrency);
            writer.WriteEndObject();
            writer.WriteString("kind", item.Kind);
            writer.WriteString("stage", item.Stage);
            writer.WriteString("status", item.Status);
            WriteOptionalNumber(writer, "elapsed_seconds", item.ElapsedSeconds);
            writer.WriteStartObject("resources");
            WriteOptionalNumber(writer, "disk_free_gb", item.Resources.DiskFreeGb);
            WriteOptionalNumber(writer, "fd_peak", item.Resources.FdPeak);
            WriteOptionalNumber(writer, "rss_peak_mb", item.Resources.RssPeakMb);
            writer.WriteEndObject();
            writer.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray());
    }

    private static bool CriticalContextMissing(PerfContext context) =>
        string.Equals(context.Commit, "unknown", StringComparison.OrdinalIgnoreCase)
        || context.LoadavgPerCpu is null
        || context.HostConcurrency is null;

    private static JsonElement RequireProperty(JsonElement parent, string name, string path)
    {
        if (!parent.TryGetProperty(name, out var value))
        {
            throw new InvalidOperationException($"required field is absent: {path}");
        }

        return value;
    }

    private static JsonElement RequireObject(JsonElement value, string path)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            throw new InvalidOperationException($"{path} must be an object");
        }

        return value;
    }

    private static string RequireString(JsonElement parent, string name, string path)
    {
        var value = RequireProperty(parent, name, path);
        if (value.ValueKind != JsonValueKind.String || string.IsNullOrWhiteSpace(value.GetString()))
        {
            throw new InvalidOperationException($"{path} must be a nonempty string");
        }

        return value.GetString()!;
    }

    private static string? OptionalString(JsonElement parent, string name, string path)
    {
        if (!parent.TryGetProperty(name, out var value) || value.ValueKind == JsonValueKind.Null)
        {
            return null;
        }

        if (value.ValueKind != JsonValueKind.String || string.IsNullOrWhiteSpace(value.GetString()))
        {
            throw new InvalidOperationException($"{path} must be null or a nonempty string");
        }

        return value.GetString();
    }

    private static double? OptionalDouble(JsonElement parent, string name, string path)
    {
        if (!parent.TryGetProperty(name, out var value) || value.ValueKind == JsonValueKind.Null)
        {
            return null;
        }

        if (value.ValueKind != JsonValueKind.Number || !value.TryGetDouble(out var number)
            || !double.IsFinite(number))
        {
            throw new InvalidOperationException($"{path} must be null or a finite number");
        }

        return number;
    }

    private static int? OptionalInt(JsonElement parent, string name, string path)
    {
        if (!parent.TryGetProperty(name, out var value) || value.ValueKind == JsonValueKind.Null)
        {
            return null;
        }

        if (value.ValueKind != JsonValueKind.Number || !value.TryGetInt32(out var number))
        {
            throw new InvalidOperationException($"{path} must be null or an integer");
        }

        return number;
    }

    private static string RequireMember(
        ImmutableHashSet<string> members,
        string value,
        string path)
    {
        if (!members.Contains(value))
        {
            throw new InvalidOperationException($"{path} has an unsupported value '{value}'");
        }

        return value;
    }

    private static void WriteOptionalString(Utf8JsonWriter writer, string name, string? value)
    {
        if (value is null) writer.WriteNull(name);
        else writer.WriteString(name, value);
    }

    private static void WriteOptionalNumber(Utf8JsonWriter writer, string name, double? value)
    {
        if (value is null) writer.WriteNull(name);
        else writer.WriteNumber(name, value.Value);
    }

    private static void WriteOptionalNumber(Utf8JsonWriter writer, string name, int? value)
    {
        if (value is null) writer.WriteNull(name);
        else writer.WriteNumber(name, value.Value);
    }
}
