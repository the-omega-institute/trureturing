using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal sealed record PerfBudget(
    string Id,
    string Mode,
    PerfCohort Cohort,
    string WorkloadId,
    string Kind,
    string Stage,
    string Metric,
    double LimitSeconds,
    string Owner,
    DateOnly ReviewDue,
    string Remediation,
    int FalsePositiveWindowDays,
    double? FalsePositiveRatePercent,
    string RollbackCriteria,
    string Source);

internal sealed record PerfBudgetCatalog(IReadOnlyList<PerfBudget> Budgets);

internal static class PerfBudgetLoader
{
    internal const string Schema = "stratalint-perf-budget-v1";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly ImmutableHashSet<string> Venues =
        ImmutableHashSet.Create(StringComparer.Ordinal, "local", "ci");
    private static readonly ImmutableHashSet<string> Kinds =
        ImmutableHashSet.Create(StringComparer.Ordinal, "timing", "resource");
    private static readonly ImmutableHashSet<string> BudgetKeys =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "id",
            "mode",
            "venue",
            "os",
            "arch",
            "cpu_class",
            "runner_class",
            "workload_id",
            "kind",
            "stage",
            "metric",
            "limit_seconds",
            "owner",
            "review_due",
            "remediation",
            "false_positive_window_days",
            "false_positive_rate_percent",
            "rollback_criteria",
            "source");

    internal static PerfBudgetCatalog LoadFile(string path)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        var fullPath = Path.GetFullPath(path);
        var bytes = File.ReadAllBytes(fullPath);
        if (bytes.Length >= 3
            && bytes[0] == 0xEF
            && bytes[1] == 0xBB
            && bytes[2] == 0xBF)
        {
            throw Invalid(fullPath, "UTF-8 BOM is forbidden");
        }
        if (bytes.AsSpan().Contains((byte)'\r'))
        {
            throw Invalid(fullPath, "CR bytes are forbidden; use LF");
        }
        if (bytes.Length == 0 || bytes[^1] != (byte)'\n')
        {
            throw Invalid(fullPath, "file must end with LF");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw Invalid(fullPath, "file must be strict UTF-8", exception);
        }

        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw Invalid(fullPath, "TOML document decoded to null");
        }
        catch (TomlException exception)
        {
            throw Invalid(fullPath, $"invalid TOML: {exception.Message}", exception);
        }

        RequireExactKeys(root, fullPath, ["schema", "budgets"]);
        if (!string.Equals(RequiredString(root, "schema", fullPath), Schema, StringComparison.Ordinal))
        {
            throw Invalid(fullPath, $"schema must be '{Schema}'");
        }
        if (root["budgets"] is not TomlTableArray tables || tables.Count == 0)
        {
            throw Invalid(fullPath, "budgets must be a non-empty table array");
        }

        var budgets = new PerfBudget[tables.Count];
        var ids = new HashSet<string>(StringComparer.Ordinal);
        var series = new HashSet<BudgetSeriesKey>();
        for (var index = 0; index < tables.Count; index++)
        {
            budgets[index] = ParseBudget(tables[index], $"{fullPath}:budgets[{index}]");
            if (!ids.Add(budgets[index].Id))
            {
                throw Invalid(fullPath, $"duplicate budget id '{budgets[index].Id}'");
            }
            var key = new BudgetSeriesKey(
                budgets[index].Cohort,
                budgets[index].WorkloadId,
                budgets[index].Kind,
                budgets[index].Stage,
                budgets[index].Metric);
            if (!series.Add(key))
            {
                throw Invalid(fullPath, $"duplicate budget series for '{budgets[index].Id}'");
            }
        }

        return new PerfBudgetCatalog(budgets);
    }

    private static PerfBudget ParseBudget(TomlTable table, string location)
    {
        var unknown = table.Keys.Where(key => !BudgetKeys.Contains(key)).Order(StringComparer.Ordinal).ToArray();
        if (unknown.Length != 0)
        {
            throw Invalid(location, $"unknown keys: {string.Join(", ", unknown)}");
        }
        var missing = BudgetKeys
            .Where(static key => key != "runner_class")
            .Where(key => !table.ContainsKey(key))
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (missing.Length != 0)
        {
            throw Invalid(location, $"missing keys: {string.Join(", ", missing)}");
        }

        var mode = RequiredString(table, "mode", location);
        if (!string.Equals(mode, "warn-only", StringComparison.Ordinal))
        {
            throw Invalid(location, "mode must be 'warn-only'");
        }
        var venue = RequiredMember(Venues, RequiredString(table, "venue", location), "venue", location);
        var kind = RequiredMember(Kinds, RequiredString(table, "kind", location), "kind", location);
        var metric = RequiredString(table, "metric", location);
        if (!string.Equals(metric, "p95_seconds", StringComparison.Ordinal))
        {
            throw Invalid(location, "metric must be 'p95_seconds'");
        }

        var reviewDueText = RequiredString(table, "review_due", location);
        if (!DateOnly.TryParseExact(
                reviewDueText,
                "yyyy-MM-dd",
                CultureInfo.InvariantCulture,
                DateTimeStyles.None,
                out var reviewDue))
        {
            throw Invalid(location, "review_due must be an ISO calendar date");
        }
        var limitSeconds = RequiredPositiveDouble(table, "limit_seconds", location);
        var falsePositiveWindowDays = RequiredPositiveInt(
            table,
            "false_positive_window_days",
            location);

        return new PerfBudget(
            RequiredString(table, "id", location),
            mode,
            new PerfCohort(
                venue,
                RequiredString(table, "os", location),
                RequiredString(table, "arch", location),
                RequiredString(table, "cpu_class", location),
                OptionalString(table, "runner_class", location)),
            RequiredString(table, "workload_id", location),
            kind,
            RequiredString(table, "stage", location),
            metric,
            limitSeconds,
            RequiredString(table, "owner", location),
            reviewDue,
            RequiredString(table, "remediation", location),
            falsePositiveWindowDays,
            RequiredFalsePositiveRate(table, location),
            RequiredString(table, "rollback_criteria", location),
            RequiredString(table, "source", location));
    }

    private static double? RequiredFalsePositiveRate(TomlTable table, string location)
    {
        var value = table["false_positive_rate_percent"];
        if (value is string text && string.Equals(text, "unmeasured", StringComparison.Ordinal))
        {
            return null;
        }
        var rate = Number(value, "false_positive_rate_percent", location);
        if (rate is < 0 or > 100)
        {
            throw Invalid(location, "false_positive_rate_percent must be 'unmeasured' or 0..100");
        }
        return rate;
    }

    private static string RequiredString(TomlTable table, string key, string location)
    {
        if (!table.TryGetValue(key, out var value)
            || value is not string text
            || string.IsNullOrWhiteSpace(text))
        {
            throw Invalid(location, $"{key} must be a non-empty string");
        }
        return text;
    }

    private static string? OptionalString(TomlTable table, string key, string location)
    {
        if (!table.TryGetValue(key, out var value)) return null;
        if (value is not string text || string.IsNullOrWhiteSpace(text))
        {
            throw Invalid(location, $"{key} must be absent or a non-empty string");
        }
        return text;
    }

    private static double RequiredPositiveDouble(TomlTable table, string key, string location)
    {
        var number = Number(table[key], key, location);
        if (!double.IsFinite(number) || number <= 0)
        {
            throw Invalid(location, $"{key} must be a positive finite number");
        }
        return number;
    }

    private static int RequiredPositiveInt(TomlTable table, string key, string location)
    {
        if (table[key] is not long value || value is <= 0 or > int.MaxValue)
        {
            throw Invalid(location, $"{key} must be a positive integer");
        }
        return (int)value;
    }

    private static double Number(object? value, string key, string location) => value switch
    {
        long integer => integer,
        double number when double.IsFinite(number) => number,
        _ => throw Invalid(location, $"{key} must be a finite number"),
    };

    private static string RequiredMember(
        ImmutableHashSet<string> members,
        string value,
        string key,
        string location)
    {
        if (!members.Contains(value))
        {
            throw Invalid(location, $"unsupported {key} '{value}'");
        }
        return value;
    }

    private static void RequireExactKeys(TomlTable table, string location, string[] expected)
    {
        var actual = table.Keys.Order(StringComparer.Ordinal).ToArray();
        var required = expected.Order(StringComparer.Ordinal).ToArray();
        if (!actual.SequenceEqual(required, StringComparer.Ordinal))
        {
            throw Invalid(location, $"keys must be exactly: {string.Join(", ", required)}");
        }
    }

    private static InvalidOperationException Invalid(
        string location,
        string message,
        Exception? inner = null) => new($"invalid performance budget '{location}': {message}", inner);

    private sealed record BudgetSeriesKey(
        PerfCohort Cohort,
        string WorkloadId,
        string Kind,
        string Stage,
        string Metric);
}
