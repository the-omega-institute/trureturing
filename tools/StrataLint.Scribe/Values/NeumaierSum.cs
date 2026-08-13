namespace StrataLint.Scribe;

public sealed class NeumaierSum
{
    private double sum;
    private double compensation;

    public long Count { get; private set; }

    public double Value => sum + compensation;

    public void Add(double value)
    {
        if (!double.IsFinite(value))
        {
            throw new ArgumentOutOfRangeException(nameof(value), "Compensated summation requires finite terms.");
        }

        var next = sum + value;
        compensation += Math.Abs(sum) >= Math.Abs(value)
            ? sum - next + value
            : value - next + sum;
        sum = next;
        Count++;
    }
}
