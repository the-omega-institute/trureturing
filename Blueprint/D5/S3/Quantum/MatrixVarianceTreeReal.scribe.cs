using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MatrixVarianceTreeRealDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/MatrixVarianceTreeReal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real positive-definite matrix weights admit a square-remainder variance identity and a positive-semidefinite defect.",
        H("Real matrix variance trees"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("family-defect-square-remainder"),
                DeclarationHandle.Create(Prefix + "family_defect_eq_square"),
                H("The family defect is a square remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty finite family of real positive-definite matrix weights and response matrices, the aggregate defect equals the sum of the centered square remainders. The center is the inverse aggregate weight multiplied by the aggregate response; every inverse and adjoint is the actual matrix operation in the Lean statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("family-defect-positive-semidefinite"),
                DeclarationHandle.Create(Prefix + "family_defect_posSemidef"),
                H("The family defect is positive semidefinite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same finite positive-definite hypotheses, the family defect is positive semidefinite. This follows from the square-remainder identity and the sum of conjugate-transpose quadratic forms, and supplies the positive matrix variance certificate used by the companion tree definitions."))),
                DescribeRole.Theorem))));
}
