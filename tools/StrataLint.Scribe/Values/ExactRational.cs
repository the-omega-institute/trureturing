using System.Globalization;
using System.Numerics;

namespace StrataLint.Scribe;

public sealed record ExactRational
{
    private ExactRational(BigInteger numerator, BigInteger denominator)
    {
        Numerator = numerator;
        Denominator = denominator;
    }

    public BigInteger Numerator { get; }

    public BigInteger Denominator { get; }

    public static ExactRational Create(BigInteger numerator, BigInteger denominator)
    {
        if (denominator.IsZero)
        {
            throw new DivideByZeroException("An exact rational denominator cannot be zero.");
        }

        if (numerator.IsZero)
        {
            return new ExactRational(BigInteger.Zero, BigInteger.One);
        }

        if (denominator.Sign < 0)
        {
            numerator = BigInteger.Negate(numerator);
            denominator = BigInteger.Negate(denominator);
        }

        var divisor = BigInteger.GreatestCommonDivisor(BigInteger.Abs(numerator), denominator);
        return new ExactRational(numerator / divisor, denominator / divisor);
    }

    public override string ToString() =>
        Denominator.IsOne
            ? Numerator.ToString(CultureInfo.InvariantCulture)
            : string.Create(
                CultureInfo.InvariantCulture,
                $"{Numerator}/{Denominator}");
}
