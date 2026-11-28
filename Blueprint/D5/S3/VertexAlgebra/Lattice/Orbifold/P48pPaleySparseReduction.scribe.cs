using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pPaleySparseReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero Paley input can be anchored with both graph weights preserved.",
        H("Anchoring P48p Paley Inputs"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-paley-support-anchoring"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseReduction.exists_anchored_paleyRow"),
            H("Projective moves and a global sign give an anchored row"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A projective move followed by an optional global sign fixes the infinity coefficient to one "
                + "and preserves both input and output Hamming weights. Weight one uses only infinity, weight "
                + "two uses infinity and zero, and weight at least three also occupies one."))),
            DescribeRole.Theorem))));
}
