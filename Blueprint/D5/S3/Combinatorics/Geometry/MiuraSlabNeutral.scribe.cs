using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabNeutralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neutral occupied strips contain both signs of actual ambient extrema.", H("Both extrema in a neutral slab"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabneutral-occupied"),
                DeclarationHandle.Create(Prefix + "RowOccupied"), H("Occupied rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A row is occupied precisely when some cell in it is a strict local minimum or maximum of the full grid, with every existing neighbour included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabneutral-cuts"),
                DeclarationHandle.Create(Prefix + "EqualRowCuts"), H("Equal signed cuts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The interval is internal, and its entire top and bottom cuts have the same specified downward height increment. These are actual edges of the same height function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabneutral-both"),
                DeclarationHandle.Create(Prefix + "neutral_row_has_both"), H("Both signs of ambient extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every unit-edge integer height array, if a nonempty internal row interval contains an occupied row and both boundary cuts have the same unit slope, the interval contains an ambient minimum and an ambient maximum. The statement includes both slope signs. One-exit rigidity excludes the absence of a maximum for increasing cuts. Reflection together with height negation gives a minimum, and negation covers decreasing cuts."))), DescribeRole.Theorem))));
}
