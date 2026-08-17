using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class MinimumMeanSquareHedgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal projection gives the unique minimum-mean-square attainable payoff.",
        H("Minimum Mean-Square Hedge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-mean-square-hedge"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/MinimumMeanSquareHedge"
                    + ".minimum_mean_square_hedge"),
                H("Orthogonal projection is the unique mean-square hedge"),
                StatementSource.FromAuthor(HedgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be an attainable-payoff subspace of a finite-dimensional real "
                        + "Hilbert space and let X be a target claim. For every Y in M, the "
                        + "squared error splits into the squared orthogonal residual and the "
                        + "squared distance from the projection to Y.")),
                    Paragraph(Text(
                        "The orthogonal projection of X onto M is characterized by an if-and-only-if "
                        + "as the unique global minimizer over M. The infimum of the squared errors "
                        + "is attained there and equals the squared residual norm.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Submodule.norm_sq_eq_add_norm_sq_starProjection "
                        + "and Submodule.starProjection_minimal as the exact projection cores. "
                        + "Repository searches found no declaration joining all three clauses."))),
                DescribeRole.Theorem))));

    private static Formula HedgeFormula()
    {
        Formula subspace = F.Id("M");
        Formula claim = F.Id("X");
        Formula payoff = F.Id("Y");
        Formula projection = Call("P", subspace, claim);
        Formula residual = Call("R", subspace, claim);
        Formula error = NormSquared(Seq(claim, Sp, Minus, Sp, payoff));

        return Disp(Seq(
            Forall, Sp, payoff, InMacro, Sp, subspace, Comma, Sp,
            error, Sp, Eq, Sp,
            NormSquared(residual), Sp, Plus, Sp,
            NormSquared(Seq(projection, Sp, Minus, Sp, payoff)), Comma, Esc,
            Operatorname, Grp(F.Id("uniqueMinimizer")), Open, error, Close,
            Sp, Eq, Sp, projection, Comma, Esc,
            Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(payoff, InMacro, Sp, subspace), Sp,
            error, Sp, Eq, Sp, NormSquared(residual), Dot));
    }

    private static Formula NormSquared(Formula value) =>
        Seq(Vert, Vert, Sp, value, Sp, Vert, Vert, Caret, Grp(D(2)));
}
