using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record CphiWindowMean(
    int FibonacciIndex,
    long StartInclusive,
    long EndExclusive,
    double Mean);

public sealed record CphiKernelResult(
    double Value,
    int TermCount,
    ImmutableArray<CphiWindowMean> WindowMeans);

public static class CphiKernel
{
    public static CphiKernelResult Compute(CphiKernelSpec spec)
    {
        ArgumentNullException.ThrowIfNull(spec);
        if (spec.TermCount < 1
            || spec.FractionalPartDecimalDigits < 1
            || spec.FirstFibonacciIndex < 2
            || spec.LastFibonacciIndex < spec.FirstFibonacciIndex)
        {
            throw new ArgumentOutOfRangeException(nameof(spec), "Cphi kernel parameters are outside the audited domain.");
        }

        var definitions = Enumerable.Range(
                spec.FirstFibonacciIndex,
                spec.LastFibonacciIndex - spec.FirstFibonacciIndex + 1)
            .Select(index => new
            {
                Index = index,
                Window = new FullPeriodWindow(
                    Label(index),
                    Fibonacci(index),
                    Fibonacci(index + 2)),
            })
            .ToArray();
        if (definitions[^1].Window.EndExclusive != spec.TermCount + 1L)
        {
            throw new ArgumentOutOfRangeException(
                nameof(spec),
                "Cphi terms must end exactly at the last declared full-period window.");
        }

        var fractionalParts = PhiFractionalPartKernel.Create(spec.FractionalPartDecimalDigits);
        var partial = new NeumaierSum();
        var windows = new FullPeriodWindowAverager(
            definitions.Select(static item => item.Window),
            FullPeriodWindowWeighting.InverseIndex);
        for (var index = 1; index <= spec.TermCount; index++)
        {
            var fraction = fractionalParts.Evaluate(index).Midpoint;
            var angle = Math.PI * fraction;
            var term = -Math.Cos(4 * angle) * (Math.Cos(angle) / Math.Sin(angle))
                / (2 * Math.PI * index);
            partial.Add(term);
            windows.Add(index, partial.Value);
        }

        var means = windows.Complete();
        var result = definitions.Select(item => new CphiWindowMean(
                item.Index,
                item.Window.StartInclusive,
                item.Window.EndExclusive,
                means[item.Window.Label]))
            .ToImmutableArray();
        return new CphiKernelResult(result[^1].Mean, spec.TermCount, result);
    }

    internal static long Fibonacci(int index)
    {
        if (index < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(index));
        }

        long previous = 0;
        long current = 1;
        for (var count = 0; count < index; count++)
        {
            checked
            {
                (previous, current) = (current, previous + current);
            }
        }

        return previous;
    }

    private static string Label(int index) => $"F{index}-F{index + 2}";
}
