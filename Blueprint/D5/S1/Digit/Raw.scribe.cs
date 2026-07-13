using System.Globalization;
using System.Numerics;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class RawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var example = new DocumentBlock.ComputedValue(
            H("Illustrative Zeckendorf normalization"),
            DeterministicComputation.Create(ComputeZeckendorfExample));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Digit/Raw",
                "Raw W digits bridge finite multiplicities to mathlib Zeckendorf lists.",
                AnchorCatalogDefinitions.GictI2Definition1_4,
                AnchorCatalogDefinitions.MathlibZeckendorfModule),
            H("Raw W-Digit Strings"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Digit/Raw"),
                    Text(" represents raw W-digit strings as finitely supported maps from indices to natural coefficients, so a digit position may temporarily carry coefficients larger than one. Evaluation multiplies each coefficient by the W weight `W_i = Fib (i + 2)` and sums; evaluation is additive.")),
                Paragraph(
                    Text("Canonical strings are the binary, nonadjacent ones. The file bridges canonical strings to the mathlib Zeckendorf representation in both directions, with the index offset `W_i = Fib (i + 2)` stated once at the bridge.")),
                example)));
    }

    // This C# helper is an illustration only; Lean remains the semantic authority for W digits.
    private static ComputedResult ComputeZeckendorfExample()
    {
        var total = new BigInteger(89) + new BigInteger(34);
        var text = "Z(89) + Z(34) = Z("
            + total.ToString(CultureInfo.InvariantCulture)
            + ") = "
            + ZeckendorfBits(total)
            + "_W";
        return new ComputedResult.Text(CanonicalComputedText.Create(text));
    }

    private static string ZeckendorfBits(BigInteger value)
    {
        if (value.Sign < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(value));
        }

        if (value.IsZero)
        {
            return "0";
        }

        var weights = new List<BigInteger> { BigInteger.One };
        if (value >= 2)
        {
            weights.Add(new BigInteger(2));
        }

        while (weights.Count >= 2)
        {
            var next = weights[^1] + weights[^2];
            if (next > value) break;
            weights.Add(next);
        }

        var remainder = value;
        var digits = new char[weights.Count];
        for (var index = weights.Count - 1; index >= 0; index--)
        {
            var outputIndex = weights.Count - 1 - index;
            if (weights[index] <= remainder)
            {
                digits[outputIndex] = '1';
                remainder -= weights[index];
            }
            else
            {
                digits[outputIndex] = '0';
            }
        }

        var result = new string(digits);
        if (!remainder.IsZero || result.Contains("11", StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Zeckendorf illustration did not normalize canonically.");
        }

        return result;
    }
}
