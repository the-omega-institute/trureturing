using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricTwentyTwoLocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Twenty Two Local", H("Symmetric Twenty Two Local"),
        Blocks(
            Paragraph(Text("Derive the local and weighted incidence identities directly from the original symmetric slice parameters and girth. These symbolic counting facts supply the high-neighbor sums and deficit bounds consumed by the profile classification.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceRigidity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting"))
        ]));
}
