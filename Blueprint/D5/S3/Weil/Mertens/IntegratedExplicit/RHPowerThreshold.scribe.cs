using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RHPowerThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp exponent for the integrated Mangoldt remainder under RH",
        H("Power normalization of the integrated Mangoldt remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("power-decay-threshold"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/RHPowerThreshold.u_div_rpow_tendsto_zero_iff"),
            H("The powers giving decay"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U, formed from the complete inclusive Mangoldt sum "
                    + "up to the natural floor of x. The variable x runs over the real axis. "
                    + "For each fixed exponent above one half and each positive tolerance, "
                    + "one cutoff controls every later x, hence every point of every later power window.")),
                Paragraph(Text(
                    "Set x = exp(y) and M = firstLiMass. Then U(x)/x^θ equals "
                    + "G(y) exp((1/2 − θ)y). Under RH the absolute value of G is eventually "
                    + "bounded by M + 1. For θ > 1/2 the exponential factor tends to zero, "
                    + "and log(x) tends to infinity with x.")),
                Paragraph(Text(
                    "The first Li coefficient gives M > 0. Given any cutoff, the recurrence "
                    + "of G supplies a natural n beyond it with G(n) > M/2. For θ ≤ 1/2 "
                    + "the exponential factor at n is at least one, so the quotient at exp(n) "
                    + "exceeds M/2. This includes θ = 1/2."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var x = F.Id("x");
        var theta = F.Id("theta");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var quotient = new Formula.Fraction(
            new Formula.Apply(F.Id("U"), [x]), F.Seq(x, F.Caret, F.Grp(theta)));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, x, F.Colon, real, F.Sp,
            F.Mapsto, F.Sp, quotient, F.Close);
        var tends = new Formula.FunctionCall(FormulaIdentifier.Create("Tendsto"),
            [function, F.Id("atTop"),
                new Formula.FunctionCall(FormulaIdentifier.Create("nhds"), [F.D(0)])]);
        var aboveHalf = new Formula.Relation(new Formula.Fraction(F.D(1), F.D(2)),
            FormulaRelationOperator.LessThan, theta);
        return F.Disp(new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Implies,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("theta"), real,
                new Formula.Logic(tends, FormulaLogicOperator.Iff, aboveHalf))));
    }
}
