using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;

namespace StrataLint.Scribe;

public sealed record KernelReceipt(
    string Kernel,
    ImmutableDictionary<string, string> Parameters,
    ImmutableDictionary<string, string> Results);

public sealed record ValueEvaluation(
    string Value,
    string Decimal,
    string Error,
    string Comparison,
    ImmutableArray<KernelReceipt> KernelReceipts);

public static class ValuesEvaluator
{
    private const int ExactDecimalDigits = 24;
    private const int EmittedDecimalPlaces = 18;
    private const int FloatingProjectionDecimalPlaces = 14;
    private const double FloatingProjectionScale = 100_000_000_000_000d;

    public static ValueEvaluation Evaluate(ValueDefinition definition)
    {
        ArgumentNullException.ThrowIfNull(definition);
        return definition.Computation switch
        {
            ValueComputation.ExactQuadratic exact => EvaluateExact(definition, exact),
            ValueComputation.Cphi cphi => EvaluateCphi(definition, cphi.Spec),
            null => throw new InvalidOperationException(
                $"Registered-open value {definition.Id} has no executable computation."),
            _ => throw new InvalidOperationException("Unknown values computation type."),
        };
    }

    private static ValueEvaluation EvaluateExact(
        ValueDefinition definition,
        ValueComputation.ExactQuadratic computation)
    {
        var phiFraction = PhiFractionalPartKernel.Create(ExactDecimalDigits).Evaluate(1);
        var sqrtLower = Add(Multiply(phiFraction.Lower, 2), ExactRational.Create(1, 1));
        var sqrtUpper = Add(Multiply(phiFraction.Upper, 2), ExactRational.Create(1, 1));
        var radicalLower = Multiply(
            computation.SqrtFiveCoefficient.Sign() < 0 ? sqrtUpper : sqrtLower,
            computation.SqrtFiveCoefficient);
        var radicalUpper = Multiply(
            computation.SqrtFiveCoefficient.Sign() < 0 ? sqrtLower : sqrtUpper,
            computation.SqrtFiveCoefficient);
        var lower = Add(computation.RationalCoefficient, radicalLower);
        var upper = Add(computation.RationalCoefficient, radicalUpper);
        var midpoint = Divide(Add(lower, upper), 2);
        var decimalValue = RoundDecimal(midpoint, EmittedDecimalPlaces);
        var parameters = ImmutableDictionary.CreateRange(
            StringComparer.Ordinal,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["decimal_digits"] = ExactDecimalDigits.ToString(CultureInfo.InvariantCulture),
                ["precision_strategy"] = PhiFractionalPartKernel.PrecisionStrategy,
                ["radicand"] = "5",
            });
        var results = ImmutableDictionary.CreateRange(
            StringComparer.Ordinal,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["decimal_lower"] = RoundDecimal(lower, EmittedDecimalPlaces + 1),
                ["decimal_upper"] = RoundDecimal(upper, EmittedDecimalPlaces + 1),
            });
        var exactValue = definition.ExactValue
            ?? throw new InvalidOperationException($"Exact value {definition.Id} has no canonical formula.");
        if (!string.Equals(definition.ReferenceValue, exactValue, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"Exact value {definition.Id} publishes reference '{definition.ReferenceValue}' "
                + $"but its canonical formula is '{exactValue}'.");
        }

        return new ValueEvaluation(
            exactValue,
            decimalValue,
            "0",
            "reference-exact",
            [new KernelReceipt("exact-quadratic", parameters, results)]);
    }

    private static ValueEvaluation EvaluateCphi(ValueDefinition definition, CphiKernelSpec spec)
    {
        var result = CphiKernel.Compute(spec);
        if (result.WindowMeans.Length < 4)
        {
            throw new InvalidOperationException(
                "Cphi projection requires at least four full-period windows for its spread estimate.");
        }

        var trailing = result.WindowMeans[^4..];
        var windowSpread = trailing.Max(static item => item.Mean)
            - trailing.Min(static item => item.Mean);
        var value = FormatFloatingProjection(result.Value);
        var error = FormatFloatingUpperBound(windowSpread);
        var fractionalParameters = Parameters(
            ("decimal_digits", spec.FractionalPartDecimalDigits.ToString(CultureInfo.InvariantCulture)),
            ("max_index", spec.TermCount.ToString(CultureInfo.InvariantCulture)),
            ("precision_strategy", PhiFractionalPartKernel.PrecisionStrategy),
            ("radicand", "5"));
        var sumParameters = Parameters(
            ("order", "ascending-k"),
            ("term_count", spec.TermCount.ToString(CultureInfo.InvariantCulture)));
        var windowParameters = Parameters(
            ("end_fibonacci_index", spec.LastFibonacciIndex.ToString(CultureInfo.InvariantCulture)),
            ("emitted_decimal_places", FloatingProjectionDecimalPlaces.ToString(CultureInfo.InvariantCulture)),
            ("error_quantization", "ceiling-at-emitted-decimal-places"),
            ("index_origin", "F0=0,F1=1"),
            ("start_fibonacci_index", spec.FirstFibonacciIndex.ToString(CultureInfo.InvariantCulture)),
            ("weighting", "inverse-index"));
        var windowResults = result.WindowMeans.ToImmutableDictionary(
            static item => $"F{item.FibonacciIndex}",
            static item => FormatFloatingProjection(item.Mean),
            StringComparer.Ordinal);
        return new ValueEvaluation(
            value,
            value,
            error,
            CompareToReference(definition, value, error),
            [
                new KernelReceipt("exact-fractional-parts", fractionalParameters, Results()),
                new KernelReceipt(
                    "neumaier-summation",
                    sumParameters,
                    Results(("summed_terms", result.TermCount.ToString(CultureInfo.InvariantCulture)))),
                new KernelReceipt("full-period-window-average", windowParameters, windowResults),
            ]);
    }

    private static string CompareToReference(ValueDefinition definition, string value, string error)
    {
        if (definition.ReferenceValue is null || definition.ReferenceError is null)
        {
            throw new InvalidOperationException(
                $"Computed value {definition.Id} has no reference to compare against.");
        }

        if (!string.Equals(definition.Error, error, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"Computed value {definition.Id} declares error '{definition.Error}' "
                + $"but its kernel produced '{error}'.");
        }

        var computed = ParseInvariant(definition.Id, "value", value);
        var reference = ParseInvariant(definition.Id, "reference_value", definition.ReferenceValue);
        var tolerance = ParseInvariant(definition.Id, "error", error)
            + ParseInvariant(definition.Id, "reference_error", definition.ReferenceError);
        return Math.Abs(computed - reference) <= tolerance
            ? "reference-consistent"
            : "reference-mismatch-open";
    }

    private static double ParseInvariant(string id, string field, string text)
    {
        if (!double.TryParse(text, NumberStyles.Float, CultureInfo.InvariantCulture, out var parsed)
            || !double.IsFinite(parsed))
        {
            throw new InvalidOperationException(
                $"Value {id} has a non-numeric {field} '{text}'.");
        }

        return parsed;
    }

    private static ImmutableDictionary<string, string> Parameters(
        params (string Key, string Value)[] items) =>
        items.ToImmutableDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);

    private static ImmutableDictionary<string, string> Results(
        params (string Key, string Value)[] items) => Parameters(items);

    private static string FormatFloatingProjection(double value) =>
        value.ToString(
            "0." + new string('0', FloatingProjectionDecimalPlaces),
            CultureInfo.InvariantCulture);

    private static string FormatFloatingUpperBound(double value)
    {
        if (!double.IsFinite(value) || value < 0)
        {
            throw new InvalidOperationException("A floating error bound must be finite and non-negative.");
        }

        return FormatFloatingProjection(
            Math.Ceiling(value * FloatingProjectionScale) / FloatingProjectionScale);
    }

    private static ExactRational Add(ExactRational left, ExactRational right) =>
        ExactRational.Create(
            left.Numerator * right.Denominator + right.Numerator * left.Denominator,
            left.Denominator * right.Denominator);

    private static ExactRational Multiply(ExactRational value, BigInteger factor) =>
        ExactRational.Create(value.Numerator * factor, value.Denominator);

    private static ExactRational Multiply(ExactRational left, ExactRational right) =>
        ExactRational.Create(
            left.Numerator * right.Numerator,
            left.Denominator * right.Denominator);

    private static ExactRational Divide(ExactRational value, BigInteger divisor) =>
        ExactRational.Create(value.Numerator, value.Denominator * divisor);

    private static int Sign(this ExactRational value) => value.Numerator.Sign;

    private static string RoundDecimal(ExactRational value, int decimalPlaces)
    {
        var scale = BigInteger.Pow(10, decimalPlaces);
        var absolute = BigInteger.Abs(value.Numerator) * scale;
        var quotient = BigInteger.DivRem(absolute, value.Denominator, out var remainder);
        if (2 * remainder >= value.Denominator)
        {
            quotient++;
        }

        var digits = quotient.ToString(CultureInfo.InvariantCulture).PadLeft(decimalPlaces + 1, '0');
        var text = decimalPlaces == 0
            ? digits
            : digits[..^decimalPlaces] + "." + digits[^decimalPlaces..];
        return value.Numerator.Sign < 0 ? "-" + text : text;
    }
}
