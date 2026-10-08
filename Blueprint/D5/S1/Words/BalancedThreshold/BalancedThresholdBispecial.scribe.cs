using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdBispecialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduce repetitions to return displacements of bispecial factors.",
        H("The general bispecial upper-bound supplier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniformly-recurrent-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/"
                    + "BalancedThresholdBispecial.UniformlyRecurrentWord"),
                H("Bounded occurrence gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each finite factor occurring in a word has an occurrence within "
                    + "a fixed distance of every suffix start. Factors use the existing "
                    + "repository wordFactor representation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bispecial-factor"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/BalancedThresholdBispecial.BispecialFactor"),
                H("Two extensions on each side"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite factor has two distinct preceding letters at positive "
                    + "occurrence starts and two distinct following letters."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacent-word-occurrences"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/"
                    + "BalancedThresholdBispecial.AdjacentOccurrences"),
                H("Adjacent occurrence starts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two occurrence starts are strictly ordered and no occurrence starts "
                    + "between them. Their displacement is a physical return length; "
                    + "the occurrences may overlap."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bispecial-return-period-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/"
                    + "BalancedThresholdBispecial.bispecial_return_period_bound"),
                H("Every periodic window obeys the return bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a uniformly recurrent word that is not eventually periodic, "
                    + "assume a positive C times the length of every nonempty bispecial "
                    + "factor is at most each adjacent return displacement. Every "
                    + "length-n window of positive period p then satisfies "
                    + "n at most (1+1/C)p. Bounded recurrence relocates the entire "
                    + "repetition away from the boundary. First failures on both sides "
                    + "produce a bispecial overlap and a return no longer than p. "
                    + "Empty overlaps are handled directly. This is a general implication; "
                    + "its recurrence and return hypotheses must be proved for the "
                    + "explicit colouring before it supplies its upper bound."))),
                DescribeRole.Theorem))));
}
