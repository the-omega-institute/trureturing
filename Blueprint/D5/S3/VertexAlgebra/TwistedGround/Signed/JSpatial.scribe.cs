using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class JSpatialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Gaussian J Spatial Equation",
        H("Signed Gaussian J Spatial Equation"),
        Blocks(
            Paragraph(Text("The regular J candidate and its chart expression have equal values away from the chart poles. The chart derivatives retain the original nonzero modeB(e)*modeB(f) term. Joint analyticity extends the equation across the same-sign diagonal; mixed chart poles are excluded by the original disk bounds.")),
            Describe.Lean(DescribeId.Create("candidatej-original-displacement"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement"), H("candidateJ_original_displacement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every Boolean label pair and real 0<r<1, with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, the signed J candidate satisfies the exact original spatial displacement equation, with the original sources, modeA, modeH, central derivative divided by period, and the additive term modeB(e)*modeB(f). Axes, origin and diagonal are included."))), DescribeRole.Theorem)
        )));
}
