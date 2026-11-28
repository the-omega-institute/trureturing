using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pOddNeighborDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-frame pairings identify the catalogue odd neighbor by a ternary syndrome.",
        H("The P48p Odd Neighbor"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-odd-neighbor-ternary-membership"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pOddNeighbor.mem_oddNeighbor_iff_ternary"),
            H("The odd neighbor is characterized by its pairing coordinates"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A rational catalogue row belongs to the odd neighbor exactly when its half-frame pairings are integral "
                + "and their residue modulo three has zero frame syndrome. The neighbor is obtained by adjoining half of "
                + "frame row zero to the integral rows pairing evenly with that frame vector."))),
            DescribeRole.Theorem))));
}
