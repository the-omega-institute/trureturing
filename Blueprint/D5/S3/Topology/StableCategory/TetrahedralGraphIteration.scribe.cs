using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class TetrahedralGraphIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refining a two-colour graph factorization",
        H("Refining a two-colour graph factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("tetrahedral-graph-refinement"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/TetrahedralGraphIteration.refine_bicolour_graphs"),
            H("One round of ordinary subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Each colour begins with a contiguity factorization through a properly two-coloured parameter graph. After three ordinary ambient subdivisions the two new induced regions factor through four subdivisions of the original parameter graphs. On the main regions the tetrahedral heights give the extra refinement. Each remaining component contracts along one opposite-colour edge and moves by an ambient edge path to the chosen parameter vertex."))),
            DescribeRole.Theorem))));
}
