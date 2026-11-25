using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtFejerWeightedMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive weighted Fejér margin for the Mangoldt remainder",
        H("The triangular average at the actual zeta zeros"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventually-positive-triangular-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.eventually_positive_triangular_margin"),
                H("A lower bound for the weighted transform"),
                StatementSource.FromAuthor(Margin()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write q(y) = exp(−y/2). For the k-th actual zero occurrence, let γₖ be its ordinate "
                        + "and aₖ its actual explicit-formula coefficient. The function W(y) sums "
                        + "|aₖ|(1 − cos(γₖy)) sinc²(q(y)yγₖ/4) over all k in ℕ. "
                        + "Under RH, conjugation pairs the contributions at positive and negative ordinates. "
                        + "The weight on a positive ordinate γ of multiplicity m is "
                        + "2m(1 − cos(γy))/(1/4 + γ²) and the triangular factor is sinc²(qyγ/4).")),
                    Paragraph(Text(
                        "The unweighted phase deficit is eventually at least qy²/64. The reciprocal-square "
                        + "tail bound makes the weight beyond a fixed cutoff in the scaled ordinate qyγ "
                        + "at most qy²/192. The cumulative zero count bounds the total weight in sufficiently "
                        + "narrow bands around the finitely many positive zeros of the triangular factor "
                        + "below that cutoff by another qy²/192. On the remaining compact set the factor "
                        + "has a positive minimum. Multiplying by the remaining weight gives one positive "
                        + "constant δ valid on a common real tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-eventually-weighted-fejer-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.rh_iff_eventually_weighted_fejer_gap"),
                H("A squared-logarithm coefficient strictly above one forty-eighth"),
                StatementSource.FromAuthor(Envelope()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here U is CompleteMertensPeak.U and the leading constant is firstLiMass. "
                        + "Average the uniform midpoint inequality against the triangular probability law "
                        + "on [0, 1/2]. Its averages of b and b/2 − b² are 1/6 and 1/24. The spectral side "
                        + "leaves the weighted transform as a positive correction to the leading coefficient "
                        + "1/48 after dividing the inequality by two.")),
                    Paragraph(Text(
                        "The error terms are o(qy²), so the forward implication keeps half the margin δ. "
                        + "Setting y = log x gives the eventual envelope with c = 1/48 + δ/2. Conversely, "
                        + "a bound with one such c implies the bounds for every coefficient below 1/48 "
                        + "because the squared logarithm is nonnegative. The finite Fejér criterion then gives RH."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Rh => Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), Real, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);

    private static Formula Margin()
    {
        var y = F.Id("y");
        var delta = F.Id("delta");
        var scale = Multiply(Call("q", y), new Formula.Power(y, D(2)));
        var tail = Bind(FormulaQuantifier.ForAll, "y",
            Implies(Le(F.Id("T"), y), Le(Multiply(delta, scale), Call("W", y))));
        var margin = Bind(FormulaQuantifier.Exists, "delta", And(Lt(D(0), delta),
            Bind(FormulaQuantifier.Exists, "T", tail)));
        return Disp(Implies(Rh, margin));
    }

    private static Formula Envelope()
    {
        var x = F.Id("x");
        var c = F.Id("c");
        var bound = Subtract(Multiply(F.Id("firstLiMass"), Seq(Sqrt, Grp(x))),
            Multiply(c, new Formula.Power(Call("log", x), D(2))));
        var tail = Bind(FormulaQuantifier.ForAll, "x",
            Implies(Le(F.Id("T"), x), Le(Call("U", x), bound)));
        var envelope = Bind(FormulaQuantifier.Exists, "c",
            And(Lt(new Formula.Fraction(D(1), D(4, 8)), c),
                Bind(FormulaQuantifier.Exists, "T", tail)));
        return Disp(new Formula.Logic(Rh, FormulaLogicOperator.Iff, envelope));
    }
}
