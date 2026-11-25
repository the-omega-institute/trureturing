using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two leading even-cutoff terms and their logarithmic average",
        H("Even truncation of the signed prime window"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-window-even-cutoff-expansion"),
                DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_expansion"),
                H("Arithmetic and spectral terms at the cutoff"),
                StatementSource.FromAuthor(Expansion()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write q=m+1=2r, s(m)=1/2−1/q and δ(m)=1/q−1/(q+1). "
                        + "For any rate v let D(v,a,B)=a^(−v)−B^(−v). "
                        + "Set W(K,m)=Kq(1+log q)². E(m,a,B) is the original signed residual "
                        + "with root degrees selected by 2n<m+1. P(r,x) is the degree-r root primitive "
                        + "over actual zeta zeros with analytic multiplicity.")),
                    Paragraph(Text("Increasing the order from m to q adds the arithmetic degree q "
                        + "and exactly the root degree r. The residual at order q is the displayed "
                        + "corrected expression. Its all-order estimate uses the faster rate s(m)+δ(m). "
                        + "Compare the two exponential integrals on the original logarithmic interval. "
                        + "The bounds include B=a."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-window-even-cutoff-cesaro"),
                DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_cesaro"),
                H("The arithmetic coefficient from fixed-width windows"),
                StatementSource.FromAuthor(Cesaro()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let F(m,L,u)=E(m,exp u,exp(u+L))/D(s(m),exp u,exp(u+L)). "
                        + "Integrable(m,L,U,T) means interval integrability of F(m,L,·) "
                        + "on [U,U+T] with respect to Lebesgue measure. "
                        + "Avg(m,L,U,T) is its interval integral divided by T. The starting threshold A "
                        + "is common to all orders and widths. The error constant depends on the order.")),
                    Paragraph(Text("Normalize the two endpoint values of the root primitive by the "
                        + "same positive gap. Under RH the resulting increment is the real part of "
                        + "an absolutely summable exponential series. The ordinates divided by r "
                        + "have magnitude at least 10/r, so integrating the series over any "
                        + "interval gives a bounded contribution. Subtract the translated primitive "
                        + "integrals before taking absolute values. The remaining two intervals have "
                        + "length L and exp(−sL)L/(1−exp(−sL)) is at most 1/s. The integral "
                        + "bound for the higher-order remainder is also uniform in L. Dividing "
                        + "by T isolates the signed arithmetic coefficient."))),
                DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [..args]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Expansion()
    {
        var m = F.Id("m");
        var r = F.Id("r");
        var q = Add(m, F.D(1));
        var a = F.Id("a");
        var b = F.Id("B");
        var threshold = F.Id("A");
        var k = F.Id("K");
        var rate = Call("s", m);
        var delta = Call("delta", m);
        var fasterRate = Add(rate, delta);
        var gap = Call("D", rate, a, b);
        var weight = Call("W", k, m);
        var fasterBound = Multiply(weight, Call("D", fasterRate, a, b));
        var arithmetic = Multiply(Multiply(Call("mu", q),
            new Formula.Fraction(q, Multiply(m, rate))), gap);
        var spectral = Multiply(Call("mu", r), Subtract(Call("P", r, b), Call("P", r, a)));
        var residual = new Formula.Absolute(Add(Add(Call("E", m, a, b), arithmetic), spectral));
        var productBound = Multiply(Multiply(Multiply(weight, new Formula.Fraction(fasterRate, rate)),
            new Formula.Power(a, new Formula.Negate(delta))), gap);
        var bounds = And(Le(residual, fasterBound), Le(fasterBound, productBound));
        var windows = All("a", Domain("R"), All("B", Domain("R"),
            Imp(And(Le(threshold, a), Le(a, b)), bounds)));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(F.D(2), m), Eq(q, Multiply(F.D(2), r))), windows)));
        return F.Disp(Imp(F.Id("RH"), Exists("A", Domain("R"), Exists("K", Domain("R"),
            And(And(Le(F.D(2), threshold), Lt(F.D(0), k)), orders)))));
    }

    private static Formula Cesaro()
    {
        var m = F.Id("m");
        var r = F.Id("r");
        var q = Add(m, F.D(1));
        var threshold = F.Id("A");
        var c = F.Id("C");
        var u = F.Id("U");
        var t = F.Id("T");
        var width = F.Id("L");
        var arithmetic = Multiply(Call("mu", q), new Formula.Fraction(q, Multiply(m, Call("s", m))));
        var error = Le(new Formula.Absolute(Add(Call("Avg", m, width, u, t), arithmetic)),
            new Formula.Fraction(c, t));
        var averages = All("U", Domain("R"), All("T", Domain("R"),
            Imp(And(Le(threshold, u), Lt(F.D(0), t)),
                And(Call("Integrable", m, width, u, t), error))));
        var widths = All("L", Domain("R"), Imp(Lt(F.D(0), width), averages));
        var exists = Exists("C", Domain("R"), And(Lt(F.D(0), c), widths));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(F.D(2), m), Eq(q, Multiply(F.D(2), r))), exists)));
        return F.Disp(Imp(F.Id("RH"), Exists("A", Domain("R"), And(Lt(F.D(0), threshold), orders))));
    }
}
