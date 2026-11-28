using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.Paley;

internal sealed class P48pFrameProjectiveActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized representative determines each projective direction over the field of 23 elements.",
        H("The P48p Projective Directions"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-frame-projective-normalization"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pFrameProjectiveAction.existsUnique_normalizedRow"),
            H("A nonzero row has a unique direction and scale"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every nonzero two-coordinate row over the field of 23 elements is a unique nonzero scalar multiple "
                + "of the chosen representative of one projective direction. The projective action uses this "
                + "factorization after right multiplication."))),
            DescribeRole.Theorem))));
}
