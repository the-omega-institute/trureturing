using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class EvenBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/EvenBound.";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/Semigroups/benfieldlippard2025positivepowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fermat divisibility produces many gaps at exponents one less than a prime.",
        H("The lower bound at prime-minus-one exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-gap-lower-bound"),
                DeclarationHandle.Create(Prefix + "even_lower"),
                H("A Fermat lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(
                    Paragraph(Text(
                        "For a prime p at least four, any representable offset below p^(p−1)−1 uses bases smaller than p. "
                        + "Fermat's little theorem makes each shifted power divisible by p. "
                        + "Counting the positive nonmultiples of p in the interval gives p^(p−1) ≤ 2|B(p−1)|. "
                        + "The lower-bound mechanism is that of Benfield and Lippard's Theorem 10.7."))
                ),
                DescribeRole.Theorem)
        )));
}
