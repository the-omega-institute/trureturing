using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FilteredVectorSpaceComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/HomologicalAlgebra/FilteredVectorSpaceComplement.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/carlsson2008zigzag");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite increasing chain of subspaces has one ambient complement that splits every layer.",
        H("Common complements for finite subspace chains"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-chain-common-complement"),
            DeclarationHandle.Create(Prefix + "exists_common_complement_of_monotone"),
            H("One complement for all layers"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let k be a division ring and V a left k-module with an additive group. "
                    + "Let F be an increasing family of submodules indexed by Fin n, and let K "
                    + "be any submodule of V. There exists a submodule L with K and L "
                    + "complementary in V such that every F(i) is the sum of its intersections "
                    + "with K and L. These intersections are disjoint because K and L are "
                    + "disjoint. Thus the same ambient splitting induces a direct sum in "
                    + "every filtration layer.")),
                Paragraph(Text(
                    "The construction proceeds along the finite chain. Inside the next layer, "
                    + "the previous partial complement is still disjoint from the intersection "
                    + "with K. It can therefore be enlarged to a complement of that intersection "
                    + "inside the next layer. The enlarged submodule contains the previous one, "
                    + "so all earlier splitting identities persist. After the last layer, an "
                    + "ambient enlargement gives a complement of K in V; containment again "
                    + "preserves every layer identity.")),
                Paragraph(Text(
                    "The empty chain, repeated layers, zero layers, and whole-space layers "
                    + "are included. Neither a zero first layer nor a whole-space last layer "
                    + "is required. The ambient dimension is unrestricted, and multiplication "
                    + "in k need not be commutative.")),
                Paragraph(Text(
                    "Carlsson and de Silva's Proposition 3.11 in arXiv:0812.0197v1, PDF pages "
                    + "13 and 14, gives the recursive complementary-summand construction for "
                    + "induced subspaces of filtered vector spaces in their finite-dimensional "
                    + "field setting. This theorem proves the division-ring, arbitrary-dimension "
                    + "version with arbitrary chain endpoints and an ambient complement. "
                    + "It does not assert an interval classification or a zigzag decomposition."))),
            DescribeRole.Theorem))));
}
