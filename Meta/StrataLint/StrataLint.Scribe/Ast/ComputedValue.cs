using System.Globalization;
using System.Numerics;

namespace StrataLint.Scribe;

public sealed record CanonicalComputedText
{
    private CanonicalComputedText(string value) => Value = value;

    public string Value { get; }

    public static CanonicalComputedText Create(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && string.Equals(value, value.Trim(), StringComparison.Ordinal)
        && value.IndexOfAny(['\r', '\n', '`']) < 0
            ? new CanonicalComputedText(value)
            : throw new ArgumentException(
                "Computed text must be one non-empty canonical line without backticks.",
                nameof(value));
}

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

public abstract record ComputedResult
{
    private ComputedResult()
    {
    }

    public sealed record Integer(BigInteger Value) : ComputedResult;

    public sealed record Decimal(decimal Value) : ComputedResult;

    public sealed record Rational(ExactRational Value) : ComputedResult;

    public sealed record Text(CanonicalComputedText Value) : ComputedResult;

    public string ToCanonicalString() => this switch
    {
        Integer integer => integer.Value.ToString(CultureInfo.InvariantCulture),
        Decimal value => value.Value.ToString("G29", CultureInfo.InvariantCulture),
        Rational { Value: not null } rational => rational.Value.ToString(),
        Text { Value: not null } text => text.Value.Value,
        _ => throw new InvalidOperationException("Computed result is malformed."),
    };
}

public sealed class DeterministicComputation
{
    public const string ProvenanceMarker =
        "⟨computed-by-C#; illustrative, not kernel-verified⟩";

    private readonly Func<ComputedResult> evaluator;

    private DeterministicComputation(Func<ComputedResult> evaluator) =>
        this.evaluator = evaluator;

    public static DeterministicComputation Create(Func<ComputedResult> evaluator)
    {
        ArgumentNullException.ThrowIfNull(evaluator);
        if (!evaluator.Method.IsStatic || evaluator.Target is not null)
        {
            throw new ArgumentException(
                "Computed C# evaluation must use a static, non-capturing delegate.",
                nameof(evaluator));
        }

        return new DeterministicComputation(evaluator);
    }

    public string EvaluateCanonical()
    {
        try
        {
            var first = evaluator()
                ?? throw new InvalidOperationException("Computed C# evaluation returned null.");
            var second = evaluator()
                ?? throw new InvalidOperationException("Computed C# evaluation returned null.");
            var firstText = first.ToCanonicalString();
            var secondText = second.ToCanonicalString();
            if (!Equals(first, second)
                || !string.Equals(firstText, secondText, StringComparison.Ordinal))
            {
                throw new InvalidOperationException(
                    "Computed C# evaluation is not deterministic across repeated evaluation.");
            }

            return firstText;
        }
        catch (InvalidOperationException exception)
            when (exception.Message.StartsWith("Computed C# evaluation", StringComparison.Ordinal))
        {
            throw;
        }
        catch (Exception exception)
        {
            throw new InvalidOperationException("computed C# evaluation failed.", exception);
        }
    }
}
