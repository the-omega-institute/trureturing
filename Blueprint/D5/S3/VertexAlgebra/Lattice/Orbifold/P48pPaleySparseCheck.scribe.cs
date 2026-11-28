using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pPaleySparseCheckDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The anchored weight-six bound completes the Paley small-support check.",
        H("The P48p Anchored Paley Checks"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-paley-sparse-check-reduction"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseCheck.paley_small_support_certificate_of_weight_six"),
            H("Weight six completes the finite checks"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The normalized checks for weights one through five already give total graph weight above twelve. "
                + "Assuming the same bound for the anchored weight-six inputs gives it for every nonzero input of "
                + "weight at most six, by the weight-preserving normalization."))),
            DescribeRole.Theorem))));
}
