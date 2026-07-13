using System.Numerics;

namespace StrataLint.Scribe;

public sealed record PhiFractionalPart(
    BigInteger Multiplier,
    BigInteger Floor,
    ExactRational Lower,
    ExactRational Upper)
{
    public double Midpoint =>
        ((double)Lower.Numerator / (double)Lower.Denominator
            + (double)Upper.Numerator / (double)Upper.Denominator) / 2;
}

public sealed class PhiFractionalPartKernel
{
    public const string PrecisionStrategy =
        "sqrt(5) is enclosed by adjacent fixed-point rationals at the declared decimal scale; "
        + "floor(n*phi) is independently exact via isqrt(5*n^2)";

    private readonly BigInteger scale;
    private readonly BigInteger sqrtFiveScaledFloor;

    private PhiFractionalPartKernel(int decimalDigits)
    {
        DecimalDigits = decimalDigits;
        scale = BigInteger.Pow(10, decimalDigits);
        sqrtFiveScaledFloor = IntegerSquareRoot(5 * scale * scale);
    }

    public int DecimalDigits { get; }

    public static PhiFractionalPartKernel Create(int decimalDigits)
    {
        if (decimalDigits is < 1 or > 100)
        {
            throw new ArgumentOutOfRangeException(
                nameof(decimalDigits),
                "Fractional-part precision must be between 1 and 100 decimal digits.");
        }

        return new PhiFractionalPartKernel(decimalDigits);
    }

    public PhiFractionalPart Evaluate(BigInteger multiplier)
    {
        if (multiplier.Sign < 0)
        {
            throw new ArgumentOutOfRangeException(
                nameof(multiplier),
                "The audited phi fractional-part kernel accepts non-negative multipliers.");
        }

        if (multiplier.IsZero)
        {
            var zero = ExactRational.Create(0, 1);
            return new PhiFractionalPart(multiplier, BigInteger.Zero, zero, zero);
        }

        var exactSqrtFloor = IntegerSquareRoot(5 * multiplier * multiplier);
        var exactFloor = (multiplier + exactSqrtFloor) / 2;
        var denominator = 2 * scale;
        var floorAtScale = 2 * exactFloor * scale;
        var lowerNumerator = multiplier * (scale + sqrtFiveScaledFloor) - floorAtScale;
        var upperNumerator = multiplier * (scale + sqrtFiveScaledFloor + 1) - floorAtScale;
        if (lowerNumerator.Sign < 0 || upperNumerator > denominator)
        {
            throw new InvalidOperationException(
                "The declared phi precision is insufficient to enclose this multiplier's fractional part.");
        }

        return new PhiFractionalPart(
            multiplier,
            exactFloor,
            ExactRational.Create(lowerNumerator, denominator),
            ExactRational.Create(upperNumerator, denominator));
    }

    internal static BigInteger IntegerSquareRoot(BigInteger value)
    {
        if (value.Sign < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(value));
        }

        if (value < 2)
        {
            return value;
        }

        var shift = checked((int)((value.GetBitLength() + 1) / 2));
        var current = BigInteger.One << shift;
        while (true)
        {
            var next = (current + value / current) >> 1;
            if (next >= current)
            {
                return current;
            }

            current = next;
        }
    }
}
