using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.Paley;

internal sealed class P48pPaleyTripleNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective permutations take any three occupied directions to the Paley anchors.",
        H("The P48p Paley Seed Triple"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-paley-seed-triple"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyTripleNormalization.exists_paleyPerm_image_triple"),
            H("Three directions can be moved to infinity, zero and one"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For any three-element subset of the 24 Paley indices, some determinant-one matrix over the "
                + "field of 23 elements sends that subset to the indices 23, zero and one. Index 23 represents infinity."))),
            DescribeRole.Theorem))));
}
