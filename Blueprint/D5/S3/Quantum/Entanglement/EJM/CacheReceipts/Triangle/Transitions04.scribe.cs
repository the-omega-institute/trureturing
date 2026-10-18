using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle;

internal sealed class Transitions04Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original triangle transitions receipts on rows 16384 through 20479",
        H("Original triangle transitions receipts on rows 16384 through 20479"),
        Blocks(
            Paragraph(Text("This same-delivery helper retains 32 original finite kernel proof blocks byte for byte. Their disjoint intervals partition [16384, 20480). The checked proposition retains every original unknown coordinate and all four value branches; no transition sample is substituted. The original root EJMTriangleCacheReceipts.transitions_accepted uses this group on its live proof path. No producer check or external evaluation replaces Lean kernel acceptance.")),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Transitions04.accepted"),
                H("Accept the exact original row interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary original row index inside [16384, 20480), exhaustive local dispatch applies its unchanged kernel receipt. The lower and upper hypotheses only select this group; the original complete root discharges them for every row."))),
                DescribeRole.Theorem))));
}
