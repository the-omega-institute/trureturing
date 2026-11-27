using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffLeftLimsupDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact left-endpoint limsup scale of the original signed prime window",
        H("The signed shrinking prime window at its left endpoint"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-left-limsup"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_left_limsup"),
            H("Finite late limsup and its sharp coefficient"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Assume Mathlib's Riemann hypothesis RH and q in H, where q is the "
                    + "constant phase i on the distinct positive zeta zeros and H is their product-topology "
                    + "phase hull. For m ≥ 2 and m + 1 = 2r, set s(m) = orderRate(m) = 1/2 − 1/(2r) "
                    + "and cₘ = μ(m+1)(m+1)/(m s(m)). "),
                    Ref("D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer")),
                Paragraph(Text("Let F(m,L,u) be signedWindowResidual at the endpoints exp(u) and exp(u+L), "
                    + "divided by powerGap with rate s(m) at the same endpoints. "
                    + "Write Q(m,r,L) for the limsup as u tends to positive infinity of "
                    + "|F(m,L,u) + cₘ + μ(r) S(r,u)|. The signal S counts the full actual zero "
                    + "occurrences with analytic multiplicity. B(m,r,L) means that the same absolute "
                    + "discrepancy is bounded above on a late tail. The width filter is the "
                    + "right-hand neighborhood filter at zero.")),
                Paragraph(Text("The left discrepancy equals the midpoint discrepancy minus μ(r) times "
                    + "the forward displacement of the root signal by L/2. The midpoint "
                    + "limsup controls the contribution of the midpoint discrepancy at lower order. "
                    + "The signed quarter-phase returns give the reverse bound for the absolute "
                    + "limsup. If μ(r) = 0, the midpoint estimate makes that limsup zero for small widths. "),
                    Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint"),
                    Text(" "),
                    Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement"))),
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
        var positiveWidths = Call("nhdsGT", Num(0));
        var bounded = Call("Eventually", WidthFunction(Call("B", m, r, width)), positiveWidths);
        var scale = Multiply(width, new Formula.Power(Call("log",
            new Formula.Fraction(Num(1), width)), Num(2)));
        var limit = new Formula.Fraction(new Formula.Absolute(Call("mu", r)),
            Multiply(Multiply(Num(4), F.Pi), Call("s", m)));
        var convergence = Call("Tendsto",
            WidthFunction(new Formula.Fraction(Call("Q", m, r, width), scale)),
            positiveWidths, Call("nhds", limit));
        var quarter = new Formula.Relation(Id("q"), FormulaRelationOperator.MemberOf, Id("H"));
        var cutoff = And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r)));
        return F.Disp(Imp(And(Id("RH"), quarter), All("m", All("r", Imp(cutoff,
            And(bounded, convergence))))));
    }
}
