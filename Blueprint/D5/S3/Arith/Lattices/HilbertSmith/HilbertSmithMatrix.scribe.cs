using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.HilbertSmith;

internal sealed class HilbertSmithMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let L be positive and divisible by the least common multiple of 1 through 2n-1. The matrix has entries L/(i+j+1) for indices from zero through n-1. The gcds of the absolute determinants of its order-k minors, for k at most n, give positive Smith factors expressed by interval least common multiples.",
        H("Smith factors of the integer Hilbert matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("det-integerhilbertminor-cast"),
                DeclarationHandle.Create(Prefix + "det_integerHilbertMinor_cast"),
                H("Cauchy formula for the actual integer minor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/krattenthaler1999determinant")),
                Blocks(Paragraph(Text(
                    "Put the chosen rows and columns in increasing order. The denominator-clearing hypothesis "
                        + "identifies each entry after rational casting with the scaled Cauchy entry. The "
                        + "determinant formula uses the ordinary row coordinates and the column coordinates shifted "
                        + "by one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integerhilbertminor-valuation"),
                DeclarationHandle.Create(Prefix + "integerHilbertMinor_valuation"),
                H("Valuation of each actual integer minor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime, twice the exponent in the absolute determinant is the doubled scale "
                        + "term plus the sum of squared discrepancies between row and reflected column residue "
                        + "counts. The Cauchy determinant is positive at a positive scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("determinantaldivisor-zero"),
                DeclarationHandle.Create(Prefix + "determinantalDivisor_zero"),
                H("The order-zero divisor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant of the empty submatrix is one, and its absolute determinant is the sole "
                        + "input to the order-zero gcd."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("determinantaldivisor-ne-zero"),
                DeclarationHandle.Create(Prefix + "determinantalDivisor_ne_zero"),
                H("Nonzero determinantal divisors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an order at most the matrix size, taking the first k rows and columns gives an "
                        + "actual minor with positive determinant at the prescribed scale. Its gcd with the other "
                        + "absolute determinants is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-integerhilbertminor-minimizer"),
                DeclarationHandle.Create(Prefix + "exists_integerHilbertMinor_minimizer"),
                H("Simultaneous attainment at each prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a prime p and let e be the base-p logarithm of 2n-1. A single pair of row "
                        + "and column sets of size k attains the bound at every layer up to e. Its "
                        + "prime exponent is k times the difference between the scale exponent and e, "
                        + "plus the sum over positive layers of the positive part of k minus capacity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("determinantaldivisor-factorization"),
                DeclarationHandle.Create(Prefix + "determinantalDivisor_factorization"),
                H("Prime exponents of the actual gcd"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exponent in the gcd is the minimum exponent of the absolute determinants. The layer "
                        + "bounds hold for every minor, and the simultaneous minimizer realizes their sum in one "
                        + "minor for the chosen prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("determinantaldivisor-succ"),
                DeclarationHandle.Create(Prefix + "determinantalDivisor_succ"),
                H("Recurrence of determinantal divisors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The divisor at order k+1 is the divisor at order k multiplied by the scale divided by "
                        + "the least common multiple from k+1 through 2n-k-1. The prime exponent increments give "
                        + "the recurrence by unique factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smithfactor-eq-intervallcm"),
                DeclarationHandle.Create(Prefix + "smithFactor_eq_intervalLCM"),
                H("Exact Smith factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an order k between one and n, the quotient of the order-k divisor by its predecessor "
                        + "is the scale divided by the least common multiple of the integers from k through 2n-k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smithfactor-pos-and-dvd"),
                DeclarationHandle.Create(Prefix + "smithFactor_pos_and_dvd"),
                H("Positive divisibility chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The symmetric intervals shrink with increasing order. Their least common multiples "
                        + "divide the scale and each divides the preceding one, so the positive scale quotients "
                        + "divide all later quotients."))),
                DescribeRole.Theorem))));
}
