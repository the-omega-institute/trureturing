using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class LiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lift", H("Lift"),
        Blocks(
            Paragraph(Text("Moderate growth of theta kernels; lifts converge, are equivariant, adjoint to descents.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/Lift.integral_lift_eq_integral_descent"),
                H("integral_lift_eq_integral_descent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The theta lifts in the two directions are transposes: for y, y' automorphic of rapid decay for S, T, ∫_{[T]} y'·(lift of y by φ) = ∫_{[S]} y·(lift of y' by φ along the swapped kernel).")))))));
}
