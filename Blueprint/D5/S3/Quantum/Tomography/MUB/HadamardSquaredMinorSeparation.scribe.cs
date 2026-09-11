using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class HadamardSquaredMinorSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared minors obstruct equivalence to a matrix with a squared row or column pair.",
        H("Hadamard Squared Minor Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minor-separation-equivalence-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/HadamardSquaredMinorSeparation."
                    + "not_hadamardEquivalent_of_squared_minor_separation"),
                H("Squared minor obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex square matrices H and K on any coordinate type, suppose "
                    + "every distinct row pair and every distinct column pair of the entrywise "
                    + "square of H has a nonzero two-by-two minor. If K has a distinct row or "
                    + "column pair whose squared minors all vanish, then H and K are not "
                    + "Hadamard equivalent."))),
                DescribeRole.Theorem))));
}
