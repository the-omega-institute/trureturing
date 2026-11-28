using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pTernaryPaleyGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ternary syndrome kernel in the signed charts is the graph of the Paley matrix.",
        H("The P48p Ternary Paley Graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-ternary-paley-graph"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pTernaryPaleyGraph.frameSyndrome_eq_zero_iff_signedChart_graph"),
            H("The signed halves characterize the kernel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A ternary row has zero frame syndrome exactly when its second signed chart half is its first "
                + "signed chart half multiplied on the right by the Paley matrix. Each chart has 24 coordinates."))),
            DescribeRole.Theorem))));
}
