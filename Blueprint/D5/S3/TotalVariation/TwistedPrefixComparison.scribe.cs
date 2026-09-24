using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TwistedPrefixComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TwistedPrefixComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform comparison for complete twisted prefixes under explicit kernel estimates.",
        H("Complete Twisted Prefix Comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twistedprefixcomparison-complete-prefix-comparison-of-estimates"),
                DeclarationHandle.Create(Prefix + "complete_prefix_comparison_of_estimates"),
                H("Length-uniform complete-prefix comparison"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume k is at least two, the parameter is positive, the loop length n plus G is at least "
                    + "two, and the reset kernel has row sums one. Let pi be a nonnegative normalized mass vector "
                    + "invariant under sign complement. If every G-step kernel entry differs from pi by at most "
                    + "epsilon, then the total variation between the normalized twisted prefix and the full Markov "
                    + "prefix is at most twice the loop length times epsilon plus the actual pi mass of suffixes at "
                    + "least that length. All n transitions are retained. The support cutoff limits the "
                    + "contributing starts by an injection into Bool times Fin of the loop length. Positive loop "
                    + "mass and the complete-prefix sum identity justify normalization. The argument does not "
                    + "require the error to be less than one. Identifying pi with a particular stationary law and "
                    + "establishing a numerical mixing rate and tail estimate are additional hypotheses to "
                    + "discharge in an application."))),
                DescribeRole.Theorem))));
}
