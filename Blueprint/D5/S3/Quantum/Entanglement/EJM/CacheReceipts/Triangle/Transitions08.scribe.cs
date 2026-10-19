using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle;

internal sealed class Transitions08Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original triangle transitions receipts on rows 32768 through 36863",
        H("Original triangle transitions receipts on rows 32768 through 36863"),
        Blocks(
            Paragraph(Text("This same-delivery helper retains 32 original finite kernel proof blocks byte for byte. Their disjoint intervals partition [32768, 36864). The checked proposition retains every original unknown coordinate and all four value branches; no transition sample is substituted. The original root EJMTriangleCacheReceipts.transitions_accepted uses this group on its live proof path. No producer check or external evaluation replaces Lean kernel acceptance.")),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Transitions08.accepted"),
                H("Accept the exact original row interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary original row index inside [32768, 36864), exhaustive local dispatch applies its unchanged kernel receipt. The lower and upper hypotheses only select this group; the original complete root discharges them for every row."))),
                DescribeRole.Theorem))));
}
