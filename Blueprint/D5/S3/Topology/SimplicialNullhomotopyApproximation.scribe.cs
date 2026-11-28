using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SimplicialNullhomotopyApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-target simplicial approximation of a nullhomotopy",
        H("Fixed-target simplicial approximation of a nullhomotopy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-target-simplicial-nullhomotopy-approximation"),
                DeclarationHandle.Create("D5/S3/Topology/SimplicialNullhomotopyApproximation.realized_simplicial_map_contracts"),
                H("Contiguity contractions from nullhomotopies of simplicial maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("A nullhomotopy of a simplicial map between finite realizations gives a single subdivision threshold of the source. At every depth past that threshold, selecting one original vertex from each refined vertex's carrier gives a composite map joined to a constant by finitely many contiguous simplicial maps in the fixed target. The proof tracks the original support under iterated barycentric averaging and uses one Lebesgue radius on the homotopy cylinder."))),
                DescribeRole.Theorem))));
}
