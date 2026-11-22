using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHWeightedPhaseLimsupDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The RH-only left-endpoint limsup formula for the signed prime window",
        H("Weighted phase alignment and the full coefficient"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-weighted-phase"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_weighted_phase"),
            H("Left-endpoint formula and exact equivalence"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix natural m and r with m ≥ 2 and m + 1 = 2r. Put "
                    + "s(m) = orderRate(m) = 1/2 − 1/(2r) and cₘ = μ(m+1)(m+1)/(m s(m)). "
                    + "At endpoints exp(u) and exp(u+L), divide signedWindowResidual by "
                    + "powerGap at rate s(m). Add cₘ and μ(r) times the root signal at u. "
                    + "The limsup of the absolute discrepancy as u tends to positive infinity "
                    + "is Qleft(m,r,L). The predicate B(m,r,L) means that the discrepancy "
                    + "is bounded above in absolute value on a late tail. Write A(m,r,L) for "
                    + "Qleft(m,r,L)/(L log²(1/L)) and κ(m,r) for |μ(r)|/(4π s(m)).")),
                Paragraph(Text("For the positive zeta zeros through the inclusive cutoff T, "
                    + "with analytic multiplicities, W(T) is the harmonic mass and P(T) is "
                    + "the real supremum of the corresponding finite weighted sine polynomial. "
                    + "The deficit is D(T) = 1 − P(T)/W(T) where W(T) is positive. "
                    + "The harmonic mass asymptotic gives eventual positivity. "),
                    Ref(RHRootWeightedSineDocument.Owner)),
                Paragraph(Text("The left discrepancy equals the midpoint discrepancy minus μ(r) "
                    + "times the forward root increment by L/2. Oddness gives a uniform absolute "
                    + "upper bound for the increment. Actual orbit recurrence at each real phase "
                    + "time gives arbitrarily late signed lower estimates. The absolute limsup "
                    + "therefore differs from |μ(r)| (L/s(m)) P(2r/L) by a lower-order error. "
                    + "This comparison also covers μ(r) = 0. "),
                    Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint"),
                    Text(" "),
                    Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup")),
                Paragraph(Text("The harmonic mass divided by log²(T) tends to 1/(4π). "
                    + "At T = 2r/L the quotient log(T)/log(1/L) tends to one, and P(T)/W(T) "
                    + "lies in [0,1]. This gives the moving-coefficient formula. When μ(r) "
                    + "is nonzero, κ(m,r) is positive. The mutually inverse positive rescalings "
                    + "T = 2r/L and L = 2r/T identify the two limit filters and give the equivalence."))),
            DescribeRole.Theorem))));

    private static Formula Naturals => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals, body);
    private static Formula WidthFunction(Formula body) =>
        F.Seq(F.Open, F.LambdaLower, F.Sp, F.Id("L"), F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var width = Id("L");
        var filter = Call("nhdsGT", Num(0));
        var zero = Call("nhds", Num(0));
        var coeff = Call("kappa", m, r);
        var normalized = Call("A", m, r, width);
        var bounded = Call("Eventually", WidthFunction(Call("B", m, r, width)), filter);
        var cutoff = new Formula.Fraction(Multiply(Num(2), r), width);
        var predicted = Multiply(coeff, Subtract(Num(1), Call("D", cutoff)));
        var convergence = Call("Tendsto", WidthFunction(Subtract(normalized, predicted)), filter, zero);
        var full = Call("Tendsto", WidthFunction(normalized), filter, Call("nhds", coeff));
        var deficit = Call("Tendsto", Id("D"), Id("atTop"), zero);
        var equivalence = new Formula.Logic(full, FormulaLogicOperator.Iff, deficit);
        var nonzero = new Formula.Relation(Call("mu", r), FormulaRelationOperator.NotEqual, Num(0));
        var telescope = And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r)));
        return F.Disp(Imp(Id("RH"), All("m", All("r", Imp(telescope,
            And(bounded, And(convergence, Imp(nonzero, equivalence))))))));
    }
}
