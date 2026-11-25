using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerMultipivotReturnsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three alternating squares on the same four vertices constrain their simultaneous returns.",
        H("Simultaneous Returns over a Boolean Steiner Subloop"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-boolean-subloop-return-range"),
                DeclarationHandle.Create(Module + ".simultaneousReturns"),
                H("The exact simultaneous return range for three pivots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Embed the eight binary vectors with exclusive-or as a multiplicatively closed subset. Use the three nonidentity pivots in a subgroup of order four. On the complementary four vertices each pair of pivot matchings forms a square.")),
                    Paragraph(Text("Each square return sums the labels along two matching colours. Every edge label occurs in two of the three returns. In an abelian group where doubling is zero, the three returns therefore sum to zero. Conversely, set the label of one edge of the second colour and one edge of the third colour to the first two requested returns. The remaining labels can be zero. This realizes all compatible triples at every corner and for every starting fibre coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("steiner-centreless-boolean-product"),
                DeclarationHandle.Create(Module + ".existsCentrelessBooleanCube"),
                H("A Boolean subloop in a centreless product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Take three copies of any centreless Steiner loop with a nonidentity point. That point and the identity form a two-element subloop. Their product embeds the eight binary vectors, and the centre of the ambient product is the identity alone.")),
                    Paragraph(Text("Applying the simultaneous return criterion to this embedding with a two-element fibre rules out prescribing a return of one for just one of the squares."))),
                DescribeRole.Theorem))));
}
