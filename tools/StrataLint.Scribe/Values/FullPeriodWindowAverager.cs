using System.Collections.Immutable;

namespace StrataLint.Scribe;

public enum FullPeriodWindowWeighting
{
    Uniform,
    InverseIndex,
}

public sealed record FullPeriodWindow
{
    public FullPeriodWindow(string label, long startInclusive, long endExclusive)
    {
        if (string.IsNullOrWhiteSpace(label))
        {
            throw new ArgumentException("A full-period window needs a label.", nameof(label));
        }

        if (startInclusive < 0 || endExclusive <= startInclusive)
        {
            throw new ArgumentOutOfRangeException(
                nameof(startInclusive),
                "A full-period window must be a non-empty non-negative half-open interval.");
        }

        Label = label;
        StartInclusive = startInclusive;
        EndExclusive = endExclusive;
    }

    public string Label { get; }

    public long StartInclusive { get; }

    public long EndExclusive { get; }
}

public sealed class FullPeriodWindowAverager
{
    private readonly ImmutableArray<WindowState> windows;
    private long previousIndex = -1;

    public FullPeriodWindowAverager(
        IEnumerable<FullPeriodWindow> windows,
        FullPeriodWindowWeighting weighting = FullPeriodWindowWeighting.Uniform)
    {
        ArgumentNullException.ThrowIfNull(windows);
        var materialized = windows.OrderBy(static item => item.Label, StringComparer.Ordinal).ToArray();
        if (materialized.Length == 0
            || materialized.Any(static item => item is null)
            || materialized.Select(static item => item.Label).Distinct(StringComparer.Ordinal).Count()
                != materialized.Length)
        {
            throw new ArgumentException(
                "Full-period windows must be non-empty, non-null, and uniquely labelled.",
                nameof(windows));
        }

        Weighting = weighting;
        this.windows = materialized.Select(static item => new WindowState(item)).ToImmutableArray();
    }

    public FullPeriodWindowWeighting Weighting { get; }

    public void Add(long index, double value)
    {
        if (index <= previousIndex)
        {
            throw new ArgumentOutOfRangeException(nameof(index), "Window samples must have increasing indices.");
        }

        previousIndex = index;
        var weight = Weighting switch
        {
            FullPeriodWindowWeighting.Uniform => 1,
            FullPeriodWindowWeighting.InverseIndex when index > 0 => 1.0 / index,
            FullPeriodWindowWeighting.InverseIndex => throw new ArgumentOutOfRangeException(
                nameof(index),
                "Inverse-index window weighting requires positive sample indices."),
            _ => throw new InvalidOperationException("Unknown full-period window weighting."),
        };
        foreach (var window in windows)
        {
            if (index >= window.Window.StartInclusive && index < window.Window.EndExclusive)
            {
                window.WeightedValues.Add(weight * value);
                window.Weights.Add(weight);
            }
        }
    }

    public ImmutableDictionary<string, double> Complete()
    {
        var result = ImmutableDictionary.CreateBuilder<string, double>(StringComparer.Ordinal);
        foreach (var window in windows)
        {
            var expected = window.Window.EndExclusive - window.Window.StartInclusive;
            if (window.WeightedValues.Count != expected || window.Weights.Count != expected)
            {
                throw new InvalidOperationException(
                    $"Full-period window {window.Window.Label} received "
                    + $"{window.WeightedValues.Count} of {expected} samples.");
            }

            result.Add(window.Window.Label, window.WeightedValues.Value / window.Weights.Value);
        }

        return result.ToImmutable();
    }

    private sealed record WindowState(FullPeriodWindow Window)
    {
        internal NeumaierSum WeightedValues { get; } = new();

        internal NeumaierSum Weights { get; } = new();
    }
}
