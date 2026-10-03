using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class CubicOrbitCanonicalHeightGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical height and Galois symmetry determine the constructed cubic-orbit Gram matrix.",
        H("Canonical-Height Gram of a Cubic Orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("family-canonical-gram"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/CubicOrbitCanonicalHeightGram.mordell_family_canonical_height_gram"),
                H("Canonical-height block Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For non-torsion Mordell points with independent cubic rotations, the half-x-coordinate canonical height is positive at each point. Galois invariance and the horizontal three-rotation relation make distinct layers orthogonal and give each pair the block H times [[1,-1/2],[-1/2,1]], with positive determinant."))),
                DescribeRole.Theorem))));
}
