using System.Globalization;
using System.Numerics;
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class RawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var total = new BigInteger(89) + new BigInteger(34);
        var bits = long.Parse(
            ZeckendorfBits(total),
            NumberStyles.None,
            CultureInfo.InvariantCulture);
        var example = DocumentBlock.Describe.Example(
            DescribeId.Create("illustrative-zeckendorf-normalization"),
            H("Illustrative Zeckendorf normalization"),
            new Formula.RelationChain(
                FormulaRelationOperator.Equal,
                [
                    Add(Call("Z", Num(89)), Call("Z", Num(34))),
                    Call("Z", Num(checked((long)total))),
                    new Formula.Subscript(Num(bits), Id("W")),
                ]),
            DescribeProvenance.RepoDerived(),
            Blocks(Paragraph(Text(
                "This illustrative normalization is derived by the repository's deterministic W-digit computation.")))
        );

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Digit/Raw",
                "Raw W digits bridge finite multiplicities to mathlib Zeckendorf lists.",
                Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")),
            H("Raw W-Digit Strings"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Digit/Raw"),
                    Text(" represents raw W-digit strings as finitely supported maps from indices to natural coefficients, so a digit position may temporarily carry coefficients larger than one. Evaluation multiplies each coefficient by the W weight `W_i = Fib (i + 2)` and sums; evaluation is additive.")),
                Paragraph(
                    Text("Canonical strings are the binary, nonadjacent ones. The file bridges canonical strings to the mathlib Zeckendorf representation in both directions, with the index offset `W_i = Fib (i + 2)` stated once at the bridge.")),
                example)));
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
