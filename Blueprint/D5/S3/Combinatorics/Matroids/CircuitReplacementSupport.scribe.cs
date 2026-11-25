using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitReplacementSupportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitReplacementSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Replacing one basis vector confines the change in an old alternating coefficient.",
        H("Support of an Alternating Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("old-coordinate-support"),
                DeclarationHandle.Create(Module + ".oldCoordinateSupport"),
                H("Coordinates read by an old coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a selected index and a finite coordinate set, include the original set."
                    + " If it contains the selected index, also include every same-size set obtained by replacing that index with one outside the original set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("disjoint-old-coordinate-support"),
                DeclarationHandle.Create(Module + ".disjoint_old_coordinate_support"),
                H("Disjoint replacement supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two sets of equal size intersecting in at most their size minus two indices have disjoint replacement supports for any selected index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("old-coordinate-zero-of-replacement-support"),
                DeclarationHandle.Create(Module + ".old_coordinate_zero_of_replacement_support"),
                H("Transport of vanishing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two ordered bases agreeing away from the selected index, an old alternating coefficient vanishes if the new coefficients on its replacement support all vanish."
                    + " Expansion in the one changed coordinate uses only these coefficients, because terms with repeated inputs vanish."))),
                DescribeRole.Theorem))));
}
