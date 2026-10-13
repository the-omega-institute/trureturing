using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMNoiseRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMNoiseRegion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete strictly nonlocal independent-source noise region",
        H("A concrete strictly nonlocal independent-source noise region"),
        Blocks(
            Paragraph(Text("Each of the three parameters is the visibility of its own physical quantum source in the concrete EJM Born law. The radius uses the exact certificate margin and a full coefficient-tree amplitude bound. It is conservative and supplies an explicit open box adjacent to the ideal point; it is not claimed to be an optimal noise threshold.")),
            Describe.Lean(DescribeId.Create("actual-noise-box"),
                DeclarationHandle.Create(Prefix + "actual_noise_box"), H("A positive box of actual nonlocal noisy laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit radius 6987435 / (24576 * 53480245575024) is positive. If all three source visibilities lie above 1 minus that radius and at most 1, their actual quantum-source noisy EJM distribution is triangle nonlocal. The actual global margin and every original F1 coefficient bound are discharged in this delivery; no abstract margin or amplitude premise remains. Source registration remains unfinished under issue #16309."))), DescribeRole.Theorem))));
}
