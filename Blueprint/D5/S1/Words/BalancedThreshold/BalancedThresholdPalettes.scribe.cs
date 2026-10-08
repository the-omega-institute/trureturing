using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdPalettesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the constant-gap palettes on mechanical occurrence ranks.",
        H("Mechanical colouring with two disjoint palettes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coloured-mechanical-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/"
                    + "BalancedThresholdPalettes.colouredMechanicalWord"),
                H("Zero-phase palette colouring"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "True occurrences alternate between two colours. False occurrence ranks "
                    + "interleave disjoint cycles of sizes t and t+1, producing 2t+3 letters."))),
                DescribeRole.Definition))));
}
