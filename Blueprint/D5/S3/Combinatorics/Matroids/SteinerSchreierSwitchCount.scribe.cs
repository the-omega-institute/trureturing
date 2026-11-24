using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSchreierSwitchCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed component returns give a count of starts in a labelled triple system.",
        H("Labelled Steiner Switch Counts from Central Returns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-schreier-labelled-switch-count"),
                DeclarationHandle.Create(Module + ".realizeLabelledSwitchCount"),
                H("Realizing a prescribed switch count on finite labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Extensions),
                Blocks(
                    Paragraph(Text("Fix a finite centreless Steiner loop, two distinct nonidentity pivots, and a finite abelian group of exponent at most two. The graph records the two pivot matchings. Prescribe a return on each connected component other than the component of the identity.")),
                    Paragraph(Text("The theorem labels the extension so the adjoined option point is its identity. It gives the deleted label and the retained pivot corresponding to the two given pivots, a complete Steiner triple system, and its matching of uncovered pairs after deletion.")),
                    Paragraph(Text("A successful starting label corresponds exactly to a point where the two matching translations have unequal endpoints in the two possible orders. This is equivalent to failing to return after two rounds. The eligible quotient points are those that fail to return after two rounds or belong to a nonidentity component with nonzero prescribed return. Every eligible quotient point contributes its full fibre, whose size is the order of the additive group."))),
                DescribeRole.Theorem))));
}
