using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class OrderedSlaterPurityDropFirstOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first-order lower bound and its equality criterion for the Slater purity drop.",
        H("First-order correction to the Slater purity-drop bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-marginal-purity-drop-first-order"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropFirstOrder.orderedMarginal_purity_drop_first_order"),
                H("Mean excesses on the binary solution set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Balance one retained pair while fixing the other endpoint probabilities. " +
                    "Assume the ordinary marginal purity decreases strictly. Restrict the " +
                    "alternation matrix to nondeterministic discarded pairs and to the selected " +
                    "retained row and the other balanced rows. The chosen basis columns determine " +
                    "their difference bits from the free bits. The free bits are independent, " +
                    "with bit-one probability twice the product of the two endpoint probabilities. " +
                    "Divide each basis-bit probability and each other biased retained parity factor " +
                    "by its positive lower bound. The result is one plus a nonnegative relative " +
                    "excess. The original product lower bound, multiplied by one plus the expected " +
                    "sum of these excesses, still lower bounds the purity drop. Equality holds exactly " +
                    "when every feasible difference string makes at most one relative excess positive. " +
                    "In the product expansion, every omitted term is nonnegative and any two " +
                    "positive excesses give a positive quadratic term. Every free assignment has " +
                    "positive probability, so that term forces a strict gap."))),
                DescribeRole.Theorem))));
}
