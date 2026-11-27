using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisContactWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even endpoint with the specified displacement supplies a witness at the corresponding little-endian index.",
        H("Realized contact masks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realized-clause"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisContactWitnesses.realized_clause"),
                H("Realized contact masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An even endpoint with the specified displacement supplies a witness at the corresponding little-endian index."))),
                DescribeRole.Theorem)),
        []));
}
