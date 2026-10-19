using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.CacheReceipts.Singleton;

internal sealed class Mirror01Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original singleton mirror receipts on rows 4096 through 8191",
        H("Original singleton mirror receipts on rows 4096 through 8191"),
        Blocks(
            Paragraph(Text("This same-delivery helper retains 32 original finite kernel proof blocks byte for byte. Their disjoint intervals partition [4096, 8192). The checked proposition contains the original assignment and lower fields. The original root EJMSingletonCacheReceipts.mirror_accepted uses this group on its live proof path. No producer check or external evaluation replaces Lean kernel acceptance.")),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/CacheReceipts/Singleton/Mirror01.accepted"),
                H("Accept the exact original row interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary original row index inside [4096, 8192), exhaustive local dispatch applies its unchanged kernel receipt. The lower and upper hypotheses only select this group; the original complete root discharges them for every row."))),
                DescribeRole.Theorem))));
}
