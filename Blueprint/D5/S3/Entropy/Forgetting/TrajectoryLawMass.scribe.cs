using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class TrajectoryLawMassDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Entropy/Forgetting/TrajectoryLawMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic trajectory laws conserve total mass and preserve nonnegativity.",
        H("Trajectory Law Mass"),
        Blocks(
            Paragraph(Text(
                "The frozen module Entropy/Forgetting/TrajectoryEntropyTelescoping defines "
                    + "trajectoryLaw update initial by recursion on time: the law at time 0 is "
                    + "initial, and the law at time k + 1 is the pushforward of the law at time k "
                    + "along update. Its type is fixed to the reals, so both statements below are "
                    + "real-valued.")),
            Paragraph(Text(
                "Beyond the Fintype instance on Y, which the finite sums need, the mass "
                    + "identity carries no hypothesis. It is stated as an equality between the "
                    + "total mass at time k and the total mass of initial, so it holds for an "
                    + "arbitrary real weighting: neither nonnegativity nor normalisation of "
                    + "initial is used, and nothing is assumed about update.")),
            Paragraph(Text(
                "The induction step is Mathlib's Finset.sum_fiberwise, restated in the "
                    + "indicator-weighted form that pushforward is written in. The mathematical "
                    + "content of the step is Mathlib's; this module supplies the statement about "
                    + "trajectoryLaw, which Mathlib cannot state because trajectoryLaw is a "
                    + "definition of this development.")),
            Paragraph(Text(
                "Two modules each carry private copies of both facts about trajectoryLaw: "
                    + "Entropy/Forgetting/TrajectoryEntropyTelescoping and "
                    + "Entropy/Forgetting/DeterministicEntropyStep, four private declarations "
                    + "under these names. Each private mass copy assumes that initial sums to one "
                    + "and concludes that the law sums to one. Reading those proofs, the "
                    + "hypothesis enters only through the base case; the successor branch "
                    + "establishes that the mass at time k+1 equals the mass at time k without "
                    + "using it, and then closes with the induction hypothesis. That is why the "
                    + "mass statement here drops the hypothesis and names the conserved quantity "
                    + "instead. This count is of declarations about trajectoryLaw under those "
                    + "two names; it is not a count of every place the one-step fact appears.")),
            Paragraph(Text(
                "Both modules are frozen, and so is TrajectoryEntropyTelescoping, which supplies "
                    + "the definition. Being frozen, neither can import this module, and this "
                    + "change removes none of the four private copies. This module has zero "
                    + "consumers today.")),
            Describe.Lean(
                DescribeId.Create("trajectory-law-sum-eq"),
                DeclarationHandle.Create(DeclarationPrefix + "trajectoryLaw_sum_eq"),
                H("Deterministic trajectories conserve total mass"),
                StatementSource.FromAuthor(SumEqFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The state type Y carries a Fintype instance and is otherwise arbitrary, "
                        + "update is an arbitrary function, initial is an arbitrary real "
                        + "weighting, and the time k is an arbitrary natural number. Beyond that "
                        + "instance there are no hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trajectory-law-nonneg"),
                DeclarationHandle.Create(DeclarationPrefix + "trajectoryLaw_nonneg"),
                H("Deterministic trajectories preserve nonnegativity"),
                StatementSource.FromAuthor(NonnegFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Beyond the Fintype instance on Y, pointwise nonnegativity of initial is "
                        + "the only hypothesis. No normalisation is required, and update is "
                        + "arbitrary."))),
                DescribeRole.Theorem))));

    private static Formula SumEqFormula()
    {
        Formula yType = F.Id("Y");
        Formula update = F.Id("update");
        Formula initial = F.Id("initial");
        Formula k = F.Id("k");
        Formula y = F.Id("y");
        Formula reals = F.Id("R");
        Formula law = Apply(F.Id("trajectoryLaw"), Seq(update, Sp, initial, Sp, k, Sp, y));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, yType, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), yType)), Comma),
            Seq(
                Forall, Sp, update, Colon, Sp, Arrow(yType, yType), Comma, Sp,
                initial, Colon, Sp, Arrow(yType, reals), Comma),
            Seq(
                Forall, Sp, k, Colon, Sp, F.Id("N"), Comma),
            Seq(
                FiniteSum(y, law), Sp, Eq, Sp,
                FiniteSum(y, Apply(initial, y)), Dot),
        ]));
    }

    private static Formula NonnegFormula()
    {
        Formula yType = F.Id("Y");
        Formula update = F.Id("update");
        Formula initial = F.Id("initial");
        Formula k = F.Id("k");
        Formula y = F.Id("y");
        Formula reals = F.Id("R");
        Formula zero = Num(0);
        Formula law = Apply(F.Id("trajectoryLaw"), Seq(update, Sp, initial, Sp, k, Sp, y));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, yType, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), yType)), Comma),
            Seq(
                Forall, Sp, update, Colon, Sp, Arrow(yType, yType), Comma, Sp,
                initial, Colon, Sp, Arrow(yType, reals), Comma),
            Seq(
                Parenthesized(Seq(Forall, Sp, y, Comma, Sp, zero, Sp, Le, Sp,
                    Apply(initial, y))), Sp, Implies),
            Seq(
                Forall, Sp, k, Sp, y, Comma, Sp, zero, Sp, Le, Sp, law, Dot),
        ]));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typeclass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula FiniteSum(Formula index, Formula summand) =>
        Seq(Sum, Underscore, Grp(index), Sp, summand);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
