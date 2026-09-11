using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenDynamicalDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Characterizations/GoldenDynamicalDeterminant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden rational continuation has two simple poles, the exact trace-series convergence radius, and the Perron rate of independently defined forbidden-11 words.",
        H("Golden Dynamical Determinant"),
        Blocks(
            Paragraph(Text(
                "The source is Part1739 of OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY. "
                    + "The local trace logarithm identifies the positive exponential with the "
                    + "rational continuation on its disk. The continuation and independently "
                    + "recursive forbidden-11 words determine the poles, Perron rate, and parity.")),
            Describe.Lean(DescribeId.Create("grounded-word-count"),
                DeclarationHandle.Create(Prefix + "wordCount"), H("Independently grounded words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count is the cardinality of the recursive Adm subtype. "
                        + "Admissibility is equivalent to no two adjacent letters "
                        + "being both true, including the empty and one-letter cases. These free "
                        + "word counts differ from the traces, which count marked closed walks."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("continuation-contract"),
                DeclarationHandle.Create(Prefix + "continuationContract"), H("Continuation and Perron contract"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The continuation is analytic off the roots and meromorphic everywhere, "
                        + "with order minus one at both roots and no other poles. The positive "
                        + "pole is the unique nearest pole. A harmonic term "
                        + "plus an absolutely summable correction gives boundary divergence and "
                        + "the greatest centered disk of absolute summability. The spectrum consists "
                        + "of the golden ratio and its negative reciprocal. The golden ratio is "
                        + "the spectral radius and has a positive Perron eigenvector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("word-contract"),
                DeclarationHandle.Create(Prefix + "wordContract"), H("Integrality, growth, and parity contract"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every length the true finite cardinality is the Fibonacci number at "
                        + "length plus two. The actual nth-root limit is the irrational golden "
                        + "ratio. The radical scalar definitions, reciprocal conjugate relation, "
                        + "and alternating conjugate powers are exact. The Binet word correction "
                        + "has a minus sign and exponent length plus two; it is negative at even "
                        + "lengths and positive at odd lengths."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-continuation"),
                DeclarationHandle.Create(Prefix + "golden_continuation"), H("Golden continuation and poles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Factor orders prove genuine simple poles at the reciprocal golden ratio "
                        + "and at minus the golden ratio. The negative eigenvalue is minus the "
                        + "reciprocal golden ratio, not the negative pole coordinate. The positive "
                        + "pole is nearest to zero. The harmonic boundary obstruction proves the "
                        + "exact centered convergence radius without claiming divergence at "
                        + "every other boundary point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("golden-words"),
                DeclarationHandle.Create(Prefix + "golden_words"), H("Golden word growth and parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction relates the recursive word carrier to all adjacent transitions. "
                        + "The cardinality and Binet formula give a positive normalized "
                        + "limit; continuity of real powers then gives the nth-root "
                        + "growth. Integrality holds at each finite length while the irrational "
                        + "rate is an asymptotic invariant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-specialization"),
                DeclarationHandle.Create(Prefix + "golden_dynamical_determinant"), H("Complete mathematical specialization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The local infinite trace sum is the negative principal logarithm of the "
                        + "determinant, and its positive exponential agrees with the rational "
                        + "continuation on the open disk. The continuation has two simple poles. "
                        + "The golden ratio is both the Perron rate and the irrational nth-root word-growth "
                        + "limit; its reciprocal is the positive principal pole coordinate. "
                        + "Every finite word count is an integer, and the negative conjugate "
                        + "eigenvalue gives the alternating correction in the Binet formula."))), DescribeRole.Theorem))));
}
