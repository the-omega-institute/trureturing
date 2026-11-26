using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.HilbertSmith;

internal sealed class DivisorFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflected matching capacity determines the prime exponents of successive interval least common multiple quotients.",
        H("Interval least common multiples and prime exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residueloss-sum-minimum"),
                DeclarationHandle.Create(Prefix + "residueLoss_sum_minimum"),
                H("Attained sum of layer bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sum the layerwise lower bounds for two index sets of size k. The nested residue "
                        + "minimizer attains all the bounds with one pair, so the sum of bounds is the minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("intervallcm-ne-zero"),
                DeclarationHandle.Create(Prefix + "intervalLCM_ne_zero"),
                H("Positive interval least common multiple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every member of the symmetric interval is positive when its lower endpoint is positive. "
                        + "Its least common multiple is then nonzero, with value one for an empty interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("intervallcm-dvd-of-le"),
                DeclarationHandle.Create(Prefix + "intervalLCM_dvd_of_le"),
                H("Divisibility of the interval least common multiples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Increasing the lower endpoint of the symmetric interval also decreases the upper "
                        + "endpoint. The least common multiple over the smaller interval divides the one over the "
                        + "larger interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("height-le-factorization"),
                DeclarationHandle.Create(Prefix + "height_le_factorization"),
                H("Prime powers in the denominator-clearing scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive n, the largest power of p at most 2n minus one is among the numbers whose least common "
                        + "multiple divides the scale. The base-p logarithm of that endpoint therefore bounds the "
                        + "scale exponent from below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("le-capacity-iff-exists-dvd"),
                DeclarationHandle.Create(Prefix + "le_capacity_iff_exists_dvd"),
                H("Capacity and multiples in the symmetric interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive q and k at most n, the capacity at modulus q is at least k exactly when the interval from k through 2n "
                        + "minus k contains a multiple of q. The distance from n to its closest multiple is the "
                        + "minimum of the distances to the adjacent multiples given by the quotient and remainder "
                        + "of n by q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("intervallcm-factorization"),
                DeclarationHandle.Create(Prefix + "intervalLCM_factorization"),
                H("Prime exponent of the interval least common multiple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 1 ≤ k ≤ n, the exponent counts the layers from one through the cutoff at which capacity is at least k. Divisibility "
                        + "of an interval least common multiple by a prime power is equivalent to divisibility of "
                        + "some member of the interval by that power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divisorexponent-succ-eq-intervallcm"),
                DeclarationHandle.Create(Prefix + "divisorExponent_succ_eq_intervalLCM"),
                H("Increment of the divisor exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Raising the order from k to k+1 adds one for each layer whose capacity is below k+1, "
                        + "together with the scale exponent minus the logarithmic cutoff. The complementary layers "
                        + "count the exponent in the interval least common multiple."))),
                DescribeRole.Theorem))));
}
