using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ResolventDefectRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resolvent defect identity and coercive rigidity.",
        H("Resolvent defect identity and coercive rigidity"), Blocks(
            Describe.Lean(
                DescribeId.Create("resolvent-defect-identity-and-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ResolventDefectRigidity.resolvent_defect_identity_and_bound"),
                H("Norm-saturated contraction defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For positive semidefinite finite complex matrices A and B, a contraction V with V* A V <= "
                        + "B, a vector b with norm saturation ||V b|| = ||b||, and every positive shift t, the "
                        + "resolvent scalar gap is the sum of two actual positive quadratic defects. It bounds t "
                        + "times the squared intertwining defect. Zero gap is equivalent to vanishing of both the "
                        + "vector defect and comparison defect. Norm saturation is a required hypothesis, not "
                        + "inferred from mere contractivity. This helper is consumed by the functional and "
                        + "logarithmic rigidity chain leading to actual Petz recovery; it claims no independent new "
                        + "theorem beyond that live derivation."))),
                DescribeRole.Theorem))));
}
