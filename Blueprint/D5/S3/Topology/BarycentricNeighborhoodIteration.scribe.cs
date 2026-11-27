using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BarycentricNeighborhoodIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph neighborhoods after iterated subdivision",
        H("Graph neighborhoods after iterated subdivision"),
        Blocks(Describe.Lean(
            DescribeId.Create("iterated-barycentric-full-neighborhood"),
            DeclarationHandle.Create(
                "D5/S3/Topology/BarycentricNeighborhoodIteration.containsBall_iteratedSubdivision"),
            H("Full subcomplexes retain graph neighborhoods at every depth"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Let a full subcomplex W contain every ambient vertex within graph distance D of P. " +
                "After r ordinary barycentric subdivisions, the subdivided W contains every vertex within distance D times two to the power r of the subdivided P. " +
                "The proof identifies the subdivided edges with comparable faces and reapplies the face-walk estimate because the subdivided W is full."))),
            DescribeRole.Theorem))));
}
