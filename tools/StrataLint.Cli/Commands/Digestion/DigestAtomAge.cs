using System.ComponentModel;
using System.Globalization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum DigestAgeBucket
{
    UnderSeven,
    SevenToThirteen,
    FourteenToTwentyNine,
    ThirtyToFortyFour,
    FortyFiveOrMore,
}

internal sealed record DigestAgeRecord(DateOnly FirstSeenDate, int AgeDays, DigestAgeBucket Bucket)
{
    internal string AgeBucket => DigestAtomAge.Label(Bucket);
}

internal sealed record DigestAgeHistogram(
    string SourceId,
    int Count,
    DateOnly? OldestFirstSeenDate,
    IReadOnlyDictionary<string, int> Buckets,
    IReadOnlyDictionary<string, IReadOnlyDictionary<string, int>> ByDisposition);

internal sealed record DigestAtomAge(
    IReadOnlyDictionary<string, DigestAgeRecord> Entries,
    DigestAgeHistogram Total,
    IReadOnlyList<DigestAgeHistogram> PerSource)
{
    internal static DigestAtomAge Read(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier,
        IAtomHistorySource source,
        TimeProvider timeProvider)
    {
        try
        {
            return Create(evaluation, frontier, source.Read(), timeProvider);
        }
        catch (Exception exception) when (exception is IOException or InvalidOperationException
            or FormatException or ArgumentException or TimeoutException or Win32Exception
            or UnauthorizedAccessException)
        {
            throw new AtomHistoryUnavailableException(exception.Message, exception);
        }
    }

    internal static DigestAtomAge Create(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier,
        AtomHistory history,
        TimeProvider timeProvider)
    {
        if (history.IsShallow)
            throw new InvalidOperationException("shallow git history cannot establish first_seen");
        var today = DateOnly.FromDateTime(timeProvider.GetUtcNow().UtcDateTime);
        var allAges = new Dictionary<string, DigestAgeRecord>(StringComparer.Ordinal);
        foreach (var item in evaluation.Entries)
        {
            // Resolve the immutable blob through the ledger's canonical storage reference.
            var casId = item.Entry.CasRef["sha256:".Length..];
            if (!history.FirstAdded.TryGetValue(casId, out var firstAdded))
                throw new InvalidOperationException($"atom {item.Entry.AtomId} has no git add record for "
                    + DigestionCasStore.RootPath + casId);
            var firstSeen = DateOnly.FromDateTime(firstAdded.UtcDateTime);
            var days = today.DayNumber - firstSeen.DayNumber;
            allAges.Add(item.Entry.AtomId, new DigestAgeRecord(firstSeen, days, Bucket(days)));
        }

        var ages = frontier.Entries.ToDictionary(
            static entry => entry.Entry.AtomId,
            entry => allAges[entry.Entry.AtomId],
            StringComparer.Ordinal);
        DigestAgeHistogram Histogram(string sourceId, IEnumerable<DigestionFrontierEntry> entries)
        {
            var items = entries.ToArray();
            IReadOnlyDictionary<string, int> Counts(IEnumerable<DigestionFrontierEntry> group)
            {
                var grouped = group.GroupBy(entry => ages[entry.Entry.AtomId].Bucket)
                    .ToDictionary(static bucket => bucket.Key, static bucket => bucket.Count());
                return Enum.GetValues<DigestAgeBucket>().ToDictionary(
                    Label, bucket => grouped.GetValueOrDefault(bucket), StringComparer.Ordinal);
            }

            return new DigestAgeHistogram(
                sourceId,
                items.Length,
                items.Select(entry => (DateOnly?)ages[entry.Entry.AtomId].FirstSeenDate).Min(),
                Counts(items),
                items.GroupBy(static entry => entry.PrimaryDispositionLabel, StringComparer.Ordinal)
                    .OrderBy(static group => group.Key, StringComparer.Ordinal)
                    .ToDictionary(static group => group.Key, group => Counts(group), StringComparer.Ordinal));
        }

        return new DigestAtomAge(
            ages,
            Histogram("total", frontier.Entries),
            frontier.PerSource.Select(source => Histogram(source.SourceId, frontier.Entries.Where(entry =>
                string.Equals(entry.Entry.SourceId, source.SourceId, StringComparison.Ordinal)))).ToArray());
    }

    private static DigestAgeBucket Bucket(int days) => days switch
    {
        < 7 => DigestAgeBucket.UnderSeven,
        < 14 => DigestAgeBucket.SevenToThirteen,
        < 30 => DigestAgeBucket.FourteenToTwentyNine,
        < 45 => DigestAgeBucket.ThirtyToFortyFour,
        _ => DigestAgeBucket.FortyFiveOrMore,
    };

    internal static string Label(DigestAgeBucket bucket) => bucket switch
    {
        DigestAgeBucket.UnderSeven => "<7",
        DigestAgeBucket.SevenToThirteen => "7-13",
        DigestAgeBucket.FourteenToTwentyNine => "14-29",
        DigestAgeBucket.ThirtyToFortyFour => "30-44",
        DigestAgeBucket.FortyFiveOrMore => ">=45",
        _ => throw new InvalidOperationException($"unsupported age bucket {bucket}"),
    };

    internal string RenderSummary()
    {
        var writer = new StringWriter(CultureInfo.InvariantCulture);
        writer.WriteLine();
        writer.WriteLine("## age");
        writer.WriteLine();
        writer.WriteLine("| source | <7 | 7-13 | 14-29 | 30-44 | >=45 | count | oldest_first_seen_date |");
        writer.WriteLine("| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |");
        foreach (var row in PerSource.Append(Total))
            writer.WriteLine($"| {row.SourceId} | {Counts(row.Buckets)} | {row.Count} | "
                + $"{row.OldestFirstSeenDate?.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture) ?? "none"} |");
        writer.WriteLine();
        writer.WriteLine("### age by disposition");
        writer.WriteLine();
        writer.WriteLine("| source | disposition | <7 | 7-13 | 14-29 | 30-44 | >=45 | count |");
        writer.WriteLine("| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |");
        foreach (var row in PerSource.Append(Total))
        foreach (var disposition in row.ByDisposition)
            writer.WriteLine($"| {row.SourceId} | {disposition.Key} | {Counts(disposition.Value)} | "
                + $"{disposition.Value.Values.Sum()} |");
        return writer.ToString();
    }

    private static string Counts(IReadOnlyDictionary<string, int> counts) =>
        string.Join(" | ", Enum.GetValues<DigestAgeBucket>().Select(bucket =>
            counts[Label(bucket)].ToString(CultureInfo.InvariantCulture)));
}
