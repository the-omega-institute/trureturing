using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ProportionalRefinementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/ProportionalRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized proportional pieces conserve quadratic budgets, contract quartic budgets, "
        + "and preserve a channel when the same feedback Kraus operator is used on every piece.",
        H("Proportional refinement and the actual defect"),
        Blocks(
            Describe.Lean(DescribeId.Create("proportional-refinement-quadratic-budgets"),
                DeclarationHandle.Create(Prefix + "quadratic_budgets"),
                H("Quadratic budgets are conserved"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("sumWeights"), Eq, D(1),
                    Sp, Rightarrow, Sp, F.Id("quadraticBudgets")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite coefficient family t with sum of squared moduli equal to one, "
                    + "each degree-two budget sums back to its unrefined value. The three readouts "
                    + "represent the defect, actual trace-defect budget, and the weighted ratio in "
                    + "the proposition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proportional-refinement-min-budget"),
                DeclarationHandle.Create(Prefix + "min_coordinate_budget_preserved"),
                H("The concrete squared-distance budget is conserved"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Sp,
                    Rightarrow, Sp, F.Id("sumMinWeights"), Eq, F.Id("minBudget")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source distance budget is min(p,q). Each proportional piece scales both "
                    + "coordinates by the same nonnegative squared modulus, so the finite sum of "
                    + "the minima returns the original minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proportional-refinement-quartic-budgets"),
                DeclarationHandle.Create(Prefix + "quartic_budgets"),
                H("Quartic budgets contract"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("sumWeights"), Eq, D(1),
                    Sp, Rightarrow, Sp, F.Id("quarticBudgets")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The products of two quadratic coordinate weights and an arbitrary quartic "
                    + "budget are multiplied by the fourth-power sum. The finite fourth-power sum "
                    + "is at most one by the normalized squared-modulus condition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proportional-refinement-actual-channel"),
                DeclarationHandle.Create(Prefix + "actual_channel_preserved_rectangular"),
                H("Common-feedback Kraus refinement preserves the channel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), Comma, Sp, F.Id("sumWeights"), Eq, D(1),
                    Sp, Rightarrow, Sp, F.Id("channelPreserved")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every proportional spectral piece retains the same feedback, its Kraus "
                    + "operator is the corresponding scalar multiple of the original. Summing the "
                    + "resulting conjugations recovers the original matrix channel for every input."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proportional-refinement-completeness"),
                DeclarationHandle.Create(Prefix + "completeness_preserved"),
                H("Rank-one completeness is preserved entrywise"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    F.Id("sumOuterPieces"), Eq, F.Id("outerVector")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every pair of coordinates, the outer-product contribution of the "
                    + "proportional pieces sums to the original rank-one contribution. This is "
                    + "the entrywise completeness identity used by a finite POVM refinement."))),
                DescribeRole.Theorem))));
}
