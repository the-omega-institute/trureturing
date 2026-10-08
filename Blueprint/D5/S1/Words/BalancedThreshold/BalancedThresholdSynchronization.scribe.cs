using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdSynchronizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover the palette phases from an equal coloured factor.",
        H("Synchronizing factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-palette-synchronization"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdSynchronization.palette_factor_synchronization"),
            H("One minority occurrence and two majority occurrences"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Equal coloured mechanical windows recover equal source windows. "
                + "If at least one true source letter and two false source letters "
                + "occur, the starting occurrence ranks agree modulo 2 and "
                + "2t(t+1), respectively. Physical-window induction extracts "
                + "consecutive observed ranks. The first two majority ranks "
                + "determine parity and both cycle residues; consecutive-integer "
                + "coprimality recovers the complete majority phase. No frequency "
                + "bound or irrationality hypothesis is used. This theorem does "
                + "not establish recurrence or classify Sturmian returns."))),
            DescribeRole.Theorem))));
}
