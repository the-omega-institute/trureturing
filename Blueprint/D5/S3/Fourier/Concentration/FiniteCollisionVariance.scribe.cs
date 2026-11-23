using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteCollisionVarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteCollisionVariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance bounds the amount of near-collision mass required at positive resolution.",
        H("A Variance Lower Bound for Weighted Near-Collisions"),
        Blocks(
            Paragraph(Text(
                "Let J be a finite type with decidable equality and let g and w be real-valued "
                + "functions on J. Write W for the total weight, μ for the mean frequency with "
                + "weights w/W, and V for the weighted mean of (g−μ)² with those weights. "
                + "The quantity E(p,η) is tailCollisionMass g w p η, counting all ordered "
                + "pairs of degree-p frequency sums within distance η.")),
            Describe.Lean(
                DescribeId.Create("tail-collision-mass-lower-variance"),
                DeclarationHandle.Create(Owner + ".tailCollisionMass_lower_variance"),
                H("A lower bound at finite frequency resolution"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Center the frequencies by subtracting μ. This shifts each degree-p "
                        + "frequency by the same amount pμ, so pair differences are preserved. "
                        + "The multinomial expansion of the p-th power of the weighted real "
                        + "exponential sum gives the same coefficients as the Fourier moment. "
                        + "At zero its value is Wᵖ. Differentiating twice at zero gives the "
                        + "centered second moment pVWᵖ because the first derivative of the "
                        + "single-frequency sum is zero there.")),
                    Paragraph(Text(
                        "Chebyshev's inequality puts at least three quarters of the coefficient "
                        + "mass within distance 2√(pV) of zero. When V is zero, all positive "
                        + "weight lies at the center. Partition that closed interval into "
                        + "at most floor(4√(pV)/η)+1 bins of width η. Each same-bin ordered pair "
                        + "is a near-collision. Cauchy–Schwarz bounds the sum of squared bin "
                        + "weights below by the square of the total weight in the interval "
                        + "divided by the number of bins.")),
                    Paragraph(Text(
                        "In the bounded-start certificate "), Ref(
                        "D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.exists_bounded_tail_window"),
                        Text(", set η = 2/L and δ > 0. Its strict moment budget then requires "
                            + "(9/16) K N (W/δ)^(2p) < 1 + 2L√(pV), where K = 3+π²/3 "
                            + "and N is the number of time samples. The inequality constrains "
                            + "that certificate's averaging length. The arithmetic upper bound "
                            + "for E(p,2/L) and the earliest missing window are separate questions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bound()
    {
        var weight = F.Id("W");
        var p = F.Id("p");
        var v = F.Id("V");
        var eta = F.Id("eta");
        var lhs = Multiply(new Formula.Fraction(D(9), D(1, 6)),
            new Formula.Power(weight, Multiply(D(2), p)));
        var root = Call("sqrt", Multiply(p, v));
        var rhs = Multiply(Seq(Open, Add(D(1), new Formula.Fraction(Multiply(D(4), root), eta)), Close),
            Call("E", p, eta));
        var assumptions = Seq(Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, Sp,
            D(0), Leq, Call("w", F.Id("j")), Quad, Quad,
            D(0), Lt, weight, Comma, Sp, D(0), Lt, p, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(0), Lt, eta);
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs)));
    }
}
