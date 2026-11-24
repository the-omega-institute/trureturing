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
                DescribeId.Create("steiner-centreless-boolean-obstruction"),
                DeclarationHandle.Create(Module + ".existsCentrelessObstruction"),
                H("A centreless quotient with an incompatible prescription"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Take three copies of the order-ten Steiner loop of the affine plane over the field with three elements. The centre of the product is trivial. Selecting the identity and one nonidentity point in each factor embeds the required Boolean subloop.")),
                    Paragraph(Text("With the two-element additive fibre, a return of one for only the first square and zero for the other two violates the parity equation. The obstruction occurs in a centreless Steiner loop of order one thousand."))),
                DescribeRole.Theorem))));
}
