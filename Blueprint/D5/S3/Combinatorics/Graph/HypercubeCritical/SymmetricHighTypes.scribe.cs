using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricHighTypesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric High Types", H("Symmetric High Types"),
        Blocks(
            Paragraph(Text("Classify bounded seven-point natural-valued functions with sum thirteen and square sum at most twenty-seven. Symbolic counts of the four possible values imply no zeros and exactly the two high-neighbor profiles; no graph enumeration is assumed.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim.")),
            Describe.Lean(
                DescribeId.Create("symmetric-high-types-high-type-classification"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighTypes.high_type_classification"),
                H("high type classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite set and natural-valued function bounded by three, cardinality seven, sum thirteen and square sum at most twenty-seven force no zero values and exactly the two stated multiplicity profiles. The complete original function domain remains arbitrary."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting"))
        ]));
}
