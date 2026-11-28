using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pPaleyActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed projective action preserves the total Hamming weight of a ternary Paley graph pair.",
        H("The Signed P48p Paley Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-paley-graph-weight-invariance"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleyAction.paleyRowAction_graph_weight"),
            H("Projective moves preserve total graph weight"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The signed row action commutes with right multiplication by the Paley matrix. Each action is a "
                + "signed permutation, so it preserves the Hamming weight of both halves of the graph pair."))),
            DescribeRole.Theorem))));
}
