using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class OddBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/OddBound.";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/AdditiveNumberTheory/benfieldlippard2025positivepowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small shifted powers give a conductor bound that controls the number of gaps for the neighboring odd exponents.",
        H("The upper bound at odd exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-gap-upper-bound"),
                DeclarationHandle.Create(Prefix + "odd_upper"),
                H("An upper bound from small generators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Paper),
                Blocks(
                    Paragraph(Text(
                        "Let p ≥ 193 and take a positive odd exponent k ≤ p. "
                        + "The shifted powers from bases at most ⌊p/3⌋ have gcd one. "
                        + "Modulo 2^k−1, every residue has a representative of weight at most (2^k−2)(⌊p/3⌋^k−1). "
                        + "Adding copies of 2^k−1 covers all integers beyond this conductor bound. "
                        + "The resulting comparison is 2|B(k)| < p^(p−1)."))
                ),
                DescribeRole.Theorem)
        )));
}
