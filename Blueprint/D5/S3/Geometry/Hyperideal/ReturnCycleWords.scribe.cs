using static StrataLint.Scribe.DefinitionDsl;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class ReturnCycleWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The paired face slots realize the low and high edge return cycles.",
        H("Noncommutative edge return cycles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noncommutative-low-edge-cycle"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/ReturnCycleWords.low_edge_cycle"),
                H("Low-edge return cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every group action and every x, the three actual edge-pairing steps "
                    + "send edge labels 0, 3, 5 back to label 0 while transporting x by "
                    + "v inverse, then u, then u. The three displayed EqvGen relations are "
                    + "the concrete low-edge cycle and expose the return word v inverse times u squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommutative-high-edge-cycle"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/ReturnCycleWords.high_edge_cycle"),
                H("High-edge return cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every group action and every x, the three actual edge-pairing steps "
                    + "send edge labels 1, 2, 4 back to label 1 while transporting x by "
                    + "v, then v, then u. The three displayed EqvGen relations are the "
                    + "concrete high-edge cycle and expose the return word v squared times u."))),
                DescribeRole.Theorem))));
}
