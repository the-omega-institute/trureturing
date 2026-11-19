using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalSourceModeTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Mixed Jacobi Identity on the Original Fixed Sector",
        H("The Mixed Jacobi Identity on the Original Fixed Sector"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-mode-of-opposite-dual"),
                DeclarationHandle.Create(Prefix + "source_mode_of_oppositeDual"),
                H("Source modes under the graded pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original source BPZ identity transports the opposite action on a grade dual to the actual lattice field mode."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("restore-fixed-source-opposite"),
                DeclarationHandle.Create(Prefix + "restore_fixed_source_opposite"),
                H("Finite sums of source grades"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transport holds on the full restricted dual by applying the graded relation to every direct-sum component."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-mixed-jacobi"),
                DeclarationHandle.Create(Prefix + "original_mixed_jacobi"),
                H("Mixed Jacobi on the fixed sector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one fixed and two twisted inputs, apply the original inverse of the pairing to the three finite coefficient sums. "
                    + "The first right channel becomes the actual fixed source action on the reconstructed coefficient."))),
                DescribeRole.Theorem))));
}
