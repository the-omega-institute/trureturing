using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;
internal sealed class SpectralEnvelopeParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The parameters and exact constants of the three-point probability envelope.",
        H("Spectral envelope parameters"), Blocks(
            Paragraph(Text("On 1/3 <= q <= 3/8 put d = sqrt(6q-2), x = (2+d)/6 and E(q) = [10-18q-(6q-2)d]/108. Then 1/3 <= x <= 5/12, 2x^2+(1-2x)^2=q, and x^2(1-2x)=E(q). E decreases on this interval. Its right endpoint is E(3/8)=25/864, and 1/32-25/864=1/432.")),
            Node("envelope", "The three-point envelope"),
            Node("upperCoordinate", "The repeated larger coordinate"),
            Node("threshold", "The exact sufficient threshold"),
            Node("threeSpectrum", "The abstract equality spectrum"),
            Paragraph(Text("The threshold q_c=(17-5 sqrt(5))/16 lies in [1/3,3/8] and satisfies E(q_c)=1/32. Its associated repeated coordinate is (1+sqrt(5))/8. The equality spectra here are abstract probability sequences. No physical attainability of them, or of the threshold equality spectrum, is asserted.")),
            Paragraph(Text("These scalar calculations are consumed by the finite optimization and countable passage. They do not supply an independent claim of new mathematics or an all-input physical purity premise.")))));
    private static DocumentBlock Node(string name, string title) => Describe.Lean(
        DescribeId.Create("spectral-parameter-" + name),
        DeclarationHandle.Create("D5/S3/Entropy/SpectralEnvelopeParameters." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("The definition fixes the exact real expression used in the envelope and sharpness statements."))), DescribeRole.Definition);
}
