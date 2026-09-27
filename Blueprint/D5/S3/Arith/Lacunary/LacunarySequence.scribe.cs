using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lacunary;

internal sealed class LacunarySequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lacunary/LacunarySequence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sequence whose consecutive ratios stay above a constant greater than one dominates a "
            + "geometric sequence, so only logarithmically many of its terms lie below a bound.",
        H("Lacunary sequences and their counting bound"),
        Blocks(
            Paragraph(Text(
                "Lacunarity is a lower bound on consecutive ratios, so it propagates by induction "
                    + "into a lower bound by a geometric sequence. Inverting that bound "
                    + "logarithmically is what limits how many terms can stay small.")),
            Describe.Lean(
                DescribeId.Create("lacunary-definition"),
                DeclarationHandle.Create(Prefix + "IsLacunary"),
                H("Lacunary sequences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsLacunary a c holds when c exceeds one, every term of a is positive, and c "
                        + "times a term is at most the next term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lacunary-geometric-bound"),
                DeclarationHandle.Create(Prefix + "geometric_lower_bound"),
                H("Geometric domination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a lacunary with ratio c and every index n, the initial term times the "
                        + "n-th power of c is at most the n-th term. Induction on n: the base case "
                        + "is an equality, and the step multiplies the inductive inequality by the "
                        + "positive number c and then applies the lacunarity inequality at n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lacunary-counting-bound"),
                DeclarationHandle.Create(Prefix + "card_lt_of_lacunary"),
                H("The counting bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a is lacunary with ratio c and each of its first N terms is at most x, "
                        + "then N is at most the larger of zero and the logarithm of x divided by "
                        + "the initial term, taken to base c, plus one. For a nonempty prefix the "
                        + "last of those terms gives the n-th power of c bounded by x divided by "
                        + "the initial term; positivity of the initial term permits the division, "
                        + "the logarithm to base c is increasing because c exceeds one, and the "
                        + "logarithm of a power of the base is the exponent. The empty prefix has "
                        + "no term to bound, so the conclusion there rests on the stated maximum "
                        + "being nonnegative. That maximum is necessary: for the sequence of "
                        + "powers of two with ratio two and bound one quarter, the hypothesis at "
                        + "N equal to zero holds vacuously while the logarithm plus one is "
                        + "negative."))),
                DescribeRole.Theorem)),
        []));
}
