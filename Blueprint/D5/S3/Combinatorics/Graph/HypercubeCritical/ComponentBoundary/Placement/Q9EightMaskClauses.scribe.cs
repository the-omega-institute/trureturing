using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9EightMaskClausesDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9EightMaskClauses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A realized displacement supplies an occupied pair in the normalized cube.",
        H("Witness clauses for realized masks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalizedrealizedclause"),
                DeclarationHandle.Create(Owner + "normalizedRealizedClause"),
                H("Witness clauses for realized masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness variables enumerate the even left endpoints and shift them by the displacement mask. A mask realized by the two supports gives a true witness literal. The ordinary occupancy and parity variables retain their original values."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9FiveAxisMissingContact")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoCNF"))
        ]));
}
