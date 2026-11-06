using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TernaryPhaseZeroCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementing the actual negative labels counts every integer-zero subset of a ternary source.",
        H("Exact zero-subset count for ternary physical labels"),
        Blocks(
            Describe.Lean(DescribeId.Create("ternary-physical-zero-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TernaryPhaseZeroCount.zero_subsets_card"),
                H("All ternary labels, without a balance hypothesis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural n and every u : Fin(n) -> Int, assume only that each u(i) is -1, 0 or 1. Let z, p and m be the actual cardinalities of the label filters u=0, u=1 and u=-1. The cardinality of all A : Finset(Fin(n)) with exact integer sum sum_{i in A} u(i)=0 is 2^z times choose(p+m,p). The empty subset is counted. These are subsets of physical labels: equal values at distinct labels give distinct choices. No total-sum-zero, p=m, positivity of n, injectivity or period hypothesis occurs.")),
                    Paragraph(Text("Let N be the actual negative-label filter and toggle A to A symmetric-difference N. This operation is its own inverse. Label by label, the signed sum of A equals the integer cardinality of the nonzero part of the toggled subset minus m. Thus exact zero is equivalent to choosing exactly m nonzero labels after the toggle. Splitting that subset into its zero and nonzero parts is a bijection with the product of the powerset of the z zero labels and the m-element subsets of the p+m nonzero labels. Mathlib powersetCard, card_nbij and symmetric-difference cancellation supply the finite counting APIs; binomial symmetry changes choose(p+m,m) to choose(p+m,p). Both private helpers are consumed by this proof.")),
                    Paragraph(Text("The complete telescope includes n=0, where the count is one; all-zero sources, where it is 2^n; p=0 or m=0, where only zero labels can be chosen and the count is 2^z; and arbitrary repetitions at distinct labels. For a phase or circle application, the ternary-value premise must first be proved for the actual labelled source. This arithmetic count does not construct an ordering, control prefix width, prove the full Circle conjecture, or establish a physical realization. No literature novelty or official acceptance claim is made."))),
                DescribeRole.Theorem)), []));
}
