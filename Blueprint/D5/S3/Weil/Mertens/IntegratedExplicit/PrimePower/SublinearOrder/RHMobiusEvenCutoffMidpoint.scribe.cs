using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffMidpointDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The midpoint limsup of the signed shrinking prime window",
        H("Phase recurrence and the arithmetic remainder"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-midpoint-limsup"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_midpoint_limsup"),
            H("Finite two-term midpoint limsup under RH"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let F be the original signed prime window divided by its power "
                    + "gap. For m+1=2r put s=1/2−1/(2r) and cₘ=μ(m+1)(m+1)/(ms). "
                    + "Define Q(m,r,L) as the limsup as u tends to positive infinity of "
                    + "the absolute value of F(m,L,u)+cₘ+μ(r)S(r,u+L/2), where S is the "
                    + "full actual-occurrence root spectrum. B(m,r,L) means this function "
                    + "of u is eventually bounded above. Its values are nonnegative.")),
                Paragraph(Text("The exponential window and midpoint are read from the same "
                    + "phase vector. Summable coefficient norms give uniform convergence "
                    + "of the readout, and parameter continuity of the integral gives one "
                    + "late return for the entire window. The decay estimate for the "
                    + "arithmetic remainder after division by the power gap transfers the "
                    + "spectral upper bound and that late lower bound to the original window.")),
                Paragraph(Text("Write G(r,L) for L/(8s) times log(1/L)+log(2r)−2c+1/2, "
                    + "with c=(Euler's constant−1+log(2π))/2, and "
                    + "E(C,L)=C L²(1+log(1/L))²."))),
            DescribeRole.Theorem))));

    private static Formula Numbers(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Numbers(domain), body);
    private static Formula ExistsReal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Numbers("R"), body);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var width = Id("L");
        var constant = Id("C");
        var moebius = Call("mu", r);
        var leading = Multiply(new Formula.Absolute(moebius), Call("G", r, width));
        var error = Call("E", constant, width);
        var estimate = Le(new Formula.Absolute(Subtract(Call("Q", m, r, width), leading)), error);
        var result = And(Call("B", m, r, width), estimate);
        var widths = All("L", "R", Imp(And(Lt(Num(0), width),
            Le(width, new Formula.Fraction(Num(1), Num(4)))), result));
        var cutoff = And(Le(Num(2), m),
            And(Eq(Add(m, Num(1)), Multiply(Num(2), r)), Lt(Num(0), new Formula.Absolute(moebius))));
        return F.Disp(Imp(Id("RH"), All("m", "N", All("r", "N", Imp(cutoff,
            ExistsReal("C", And(Lt(Num(0), constant), widths)))))));
    }
}
