using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class UnitaryThreeFramePotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-by-three unitary fourth frame potential is at least one.",
        H("Unitary Three Frame Potential"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "unitary-three-row-fourth-potential-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/UnitaryThreeFramePotential."
                    + "unitaryThree_row_fourthPotential_ge_one_third"),
                H("Row fourth-potential lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-by-three complex matrix whose row Gram is the identity, "
                    + "each row has sum of squared entry norm-squares at least one-third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "unitary-three-total-fourth-potential-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/UnitaryThreeFramePotential."
                    + "unitaryThree_fourthPotential_ge_one"),
                H("Total fourth-potential lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-by-three complex matrix whose row Gram is the identity, "
                    + "the sum over all entries of the square of the complex squared norm is "
                    + "at least one."))),
                DescribeRole.Theorem))));
}
