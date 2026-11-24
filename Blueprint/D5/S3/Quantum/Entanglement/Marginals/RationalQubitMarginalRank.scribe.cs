using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class RationalQubitMarginalRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational rank bound for joint positive matrices with two qubit marginals.",
        H("Low-rank rational extensions of qubit marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("rational-qubit-marginal-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank.rational_endpoint_rank_le_three"),
                H("Rational extensions of rank at most three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rational positive semidefinite joint matrix of rank at most three exists "
                    + "exactly for two qubit marginals that are positive semidefinite, have equal "
                    + "trace, and have rational real and imaginary parts in every entry. "
                    + "Taking a partial trace preserves positivity and trace and only sums entries.")),
                    Paragraph(Text(
                    "Eliminate one scalar pivot in each marginal. The resulting decomposition "
                    + "has at most two terms, each a nonnegative rational weight times a "
                    + "rank-one trace-one matrix with rational entries. When the pivot is zero, "
                    + "positivity forces its off-diagonal entry to vanish. Match the two pairs "
                    + "of weights with a two-by-two table, assigning the smaller of the first "
                    + "two weights to the first cell. At least one off-diagonal cell then "
                    + "vanishes. Sum the corresponding products of the rank-one matrices. "
                    + "Their partial traces recover the prescribed weights, and at most three "
                    + "nonzero rank-one terms contribute to the joint matrix."))),
                DescribeRole.Theorem))));
}
