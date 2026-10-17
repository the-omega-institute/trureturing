using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Triangle;

internal sealed class Mirror10Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original triangle mirror receipts on rows 40960 through 41293",
        H("Original triangle mirror receipts on rows 40960 through 41293"),
        Blocks(
            Paragraph(Text("This same-delivery helper retains 3 original finite kernel proof blocks byte for byte. Their disjoint intervals partition [40960, 41294). The checked proposition contains the original assignment and lower fields. The original root EJMTriangleCacheReceipts.mirror_accepted uses this group on its live proof path. No producer check or external evaluation replaces Lean kernel acceptance.")),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Triangle/Mirror10.accepted"),
                H("Accept the exact original row interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary original row index inside [40960, 41294), exhaustive local dispatch applies its unchanged kernel receipt. The lower and upper hypotheses only select this group; the original complete root discharges them for every row."))),
                DescribeRole.Theorem))));
}
