using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalFrequencyRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frequency Reindexing of the Original Kernels",
        H("Frequency Reindexing of the Original Kernels"),
        Blocks(
            Paragraph(Text("For a fixed second external mode, the actual signed frequency difference can be summed in the first external variable. The proof uses the literal J/T rows, normal convergence on an intermediate radius, the complex derivative of the actual row series, and the negative-zero boundary without dividing by the mode variable.")),
            Describe.Lean(
                DescribeId.Create("external-frequency-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequencyRows.external_frequency_row"),
                H("external_frequency_row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either literal J or literal T, every signed first-mode row and every fixed second mode satisfy the exact positive or negative mode-frequency differential equation on the normal-convergence disk. The false row uses the shifted p+1 tail, while the true row retains the actual false-zero boundary. No division by u is used."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-frequency-generated"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequencyRows.external_frequency_generated"),
                H("external_frequency_generated"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either literal J or T, every sign pair, and complex u,v,z with norm(u)+norm(z)<1 and norm(v)+norm(z)<1, the full product series of modeScale(e,u) times modeFrequency(e,p,K) times u^p v^q has sum u(1-u) partial_u kernelMode plus delta(e,u) kernelMode minus modeB(e) times the actual false-zero row in v. Here delta is (1-3u)/2 for the positive label and -(u+1)/2 for the negative label. Product summability is established from the original full derivative and zero/successor decompositions before Fubini. Both u=0 and v=0 are included."))), DescribeRole.Theorem))));
}
