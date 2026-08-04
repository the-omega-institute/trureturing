using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class ZetaHeatTraceBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/ZetaHeatTraceBridge",
            "The universal heat-abscissa theorem specializes to the existing labeled-zeta Hilbert criterion."),
        H("The Labeled-Zeta Heat-Trace Bridge"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-is-the-prime-axis-specialization"),
                H("Labeled zeta is the prime-axis specialization"),
                LeanTheorem(
                    "D5/S3/Midline/ZetaHeatTraceBridge.labeled_zeta_mem_iff_via_universal_heat_trace"),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2)\Leftrightarrow\frac12<\Re(s)$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "SpectralHilbert proves the established criterion by instantiating the general theorem on PrimeAxisTable with logarithmic length and abscissa one. This declaration exposes that single-source relation without adding a second analytic proof.")))))));
}
