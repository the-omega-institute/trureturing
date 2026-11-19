using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class AsymmetricSliceRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Saturated slice rigidity.", H("Saturated slice rigidity"),
        Blocks(Paragraph(Text(
            "Saturated nonbacktracking path counts force endpoint coverage and right-neighbor rigidity. A triangle-free two-regular graph on six vertices, with a distinguished nonedge having no common neighbor, admits the explicit six-cycle labeling used in the actual slice classification. The declarations are private helpers consumed by AsymmetricSliceExclusion.result. All arguments are symbolic over arbitrary finite vertex types; no enumerated graph catalog or numerical certificate is assumed."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting"))]));
}
