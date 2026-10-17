using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;
internal sealed class DivisorNimPeriodPropagationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full finite mex lookback blocks propagate equality under common forcing; singleton boards retain their actual values.",
        H("Finite mex block propagation"), Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-value"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Games/DivisorNimPeriodPropagation.singleton_grundy"),
                H("The actual singleton value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive natural n, the native Grundy value of the singleton "
                        + "multiset containing n is n. Every removal from one through n is "
                        + "legal, and the follower values are exactly zero through n minus one. "
                        + "The fixed-board recurrence and the general existence proof "
                        + "both use this fact when deletion leaves no fixed heap."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("block-propagation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Games/DivisorNimPeriodPropagation.mex_forced_block_propagation"),
                H("Propagation from a complete lookback block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every natural D and finite set B of positive delays at most D, let f and g be natural-valued sequences. If they agree below D and, at every later index t, each is the mex of the same forcing set F(t) together with its own values at all delays in B, then they agree at every index. Strong induction compares the complete predecessor images. The fixed-board eventual-periodicity proof applies this result with all positive divisors of the fixed-board gcd and the actual common follower forcing. Singleton values are reused by both fixed-board and gcd-six recurrence proofs. The moved singleton audit requires current source binding; the propagation audit remains unfinished under issue https://github.com/the-omega-institute/trureturing/issues/17433."))),
                DescribeRole.Theorem))));
}
