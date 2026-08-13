using System.Numerics;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesKernelTests
{
    [Fact]
    public void PhiFractionalPartUsesAnExactFloorAndAControlledRationalInterval()
    {
        var kernel = PhiFractionalPartKernel.Create(decimalDigits: 30);

        var result = kernel.Evaluate(new BigInteger(2));

        Assert.Equal(new BigInteger(3), result.Floor);
        Assert.True(LessThan(result.Lower, ExactRational.Create(237, 1000)));
        Assert.True(LessThan(ExactRational.Create(236, 1000), result.Upper));
        Assert.True(LessThan(
            Subtract(result.Upper, result.Lower),
            ExactRational.Create(1, BigInteger.Pow(10, 28))));
    }

    [Theory]
    [InlineData(28, 317811, 514228, true)]
    [InlineData(29, 514229, 832040, false)]
    public void PhiFractionalPartMatchesTheFibonacciConvergentIdentity(
        int fibonacciIndex,
        int multiplier,
        int expectedFloor,
        bool approachesFromBelow)
    {
        var result = PhiFractionalPartKernel.Create(decimalDigits: 40).Evaluate(multiplier);
        var phi = (1 + Math.Sqrt(5)) / 2;
        var residual = Math.Pow(phi, -fibonacciIndex);
        var expectedFraction = approachesFromBelow ? 1 - residual : residual;

        Assert.Equal(new BigInteger(expectedFloor), result.Floor);
        Assert.Equal(expectedFraction, result.Midpoint, precision: 14);
    }

    [Fact]
    public void NeumaierSummationRetainsAUnitLostByNaiveSummation()
    {
        var sum = new NeumaierSum();

        sum.Add(1e16);
        sum.Add(1);
        sum.Add(-1e16);

        Assert.Equal(1, sum.Value);
        Assert.Equal(3, sum.Count);
    }

    [Fact]
    public void FullPeriodAveragingSupportsOverlappingIndexWindows()
    {
        var averaging = new FullPeriodWindowAverager(
        [
            new FullPeriodWindow("wide", 1, 5),
            new FullPeriodWindow("inner", 2, 4),
        ]);

        averaging.Add(1, 1);
        averaging.Add(2, 3);
        averaging.Add(3, 1);
        averaging.Add(4, 3);

        var result = averaging.Complete();
        Assert.Equal(2, result["wide"]);
        Assert.Equal(2, result["inner"]);
    }

    [Fact]
    public void FullPeriodAveragingSupportsTheAuditedInverseIndexWeight()
    {
        var averaging = new FullPeriodWindowAverager(
        [
            new FullPeriodWindow("wide", 1, 5),
            new FullPeriodWindow("inner", 2, 4),
        ], FullPeriodWindowWeighting.InverseIndex);

        averaging.Add(1, 1);
        averaging.Add(2, 3);
        averaging.Add(3, 1);
        averaging.Add(4, 3);

        var result = averaging.Complete();
        Assert.Equal(43.0 / 25, result["wide"], precision: 14);
        Assert.Equal(11.0 / 5, result["inner"], precision: 14);
    }

    [Fact]
    public void CphiRejectsTermsBeyondTheLastCompleteWindow()
    {
        var spec = new CphiKernelSpec(
            TermCount: 13,
            FractionalPartDecimalDigits: 30,
            FirstFibonacciIndex: 5,
            LastFibonacciIndex: 5);

        var exception = Assert.Throws<ArgumentOutOfRangeException>(() => CphiKernel.Compute(spec));

        Assert.Contains("end exactly", exception.Message, StringComparison.Ordinal);
    }

    private static bool LessThan(ExactRational left, ExactRational right) =>
        left.Numerator * right.Denominator < right.Numerator * left.Denominator;

    private static ExactRational Subtract(ExactRational left, ExactRational right) =>
        ExactRational.Create(
            left.Numerator * right.Denominator - right.Numerator * left.Denominator,
            left.Denominator * right.Denominator);
}
