using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierFiveCrossBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transpose symmetry reduces the estimate to zero, one, or two columns when the total selected indices are at most five. The two-column Gram off-diagonal is a pentagon phase sum.",
        H("Bounds on rectangular five-point Fourier compressions"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-crossform"),
                DeclarationHandle.Create(Prefix + "crossForm"), H("The rectangular Fourier form"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The form pairs two supported coefficient vectors through the normalized Fourier entries of the corresponding rectangular submatrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-crossform-sq-le"),
                DeclarationHandle.Create(Prefix + "crossForm_sq_le"), H("The exact compression bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transpose symmetry reduces the estimate to zero, one, or two columns when the total selected indices are at most five. The two-column Gram off-diagonal is a pentagon phase sum."))), DescribeRole.Theorem)),
        []));
}
