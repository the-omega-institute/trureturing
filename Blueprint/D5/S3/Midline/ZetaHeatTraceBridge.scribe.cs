using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class ZetaHeatTraceBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/ZetaHeatTraceBridge",
            "Prime-axis logarithmic length derives the labeled-zeta Hilbert criterion from the universal heat-abscissa theorem."),
        H("The Labeled-Zeta Heat-Trace Bridge"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-is-the-prime-axis-specialization"),
                H("Labeled zeta is the prime-axis specialization"),
                LeanTheorem(
                    "D5/S3/Midline/ZetaHeatTraceBridge.zeta_mem_iff_from_universal_heat_trace"),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2)\Leftrightarrow\frac12<\Re(s)$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The bridge identifies the universal heat coefficient with the labeled-zeta coefficient, proves boundary-divergent abscissa one by transporting to the p-series on natural addresses, and then applies the universal strict theorem.")))))));
}
