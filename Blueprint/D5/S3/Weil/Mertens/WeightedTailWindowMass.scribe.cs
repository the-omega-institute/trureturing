using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedTailWindowMassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/WeightedTailWindowMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative mass under finite weighted-tail inversion",
        H("Transport across a finite window"),
        Blocks(
            Paragraph(Text("Let Q(k,x) be the tail of k from x to infinity and W(k,x) its tail "
                + "weighted by (1+log(t))/log(t)^2. Write a(t)=log(t)^2/(1+log(t)), v=a', "
                + "and E(k,B)=Q(k,B)-a(B)W(k,B). The nonlocal coefficient is "
                + "K(Y,X,t)=2(sqrt(min(t,X))-sqrt(Y))v(t).")),
            Describe.Lean(DescribeId.Create("weighted-window-majorant"),
                DeclarationHandle.Create(Module + "negative_mass_le_of_majorant"),
                H("The local, nonlocal, and endpoint contributions"),
                StatementSource.FromAuthor(Claim(exact: true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Invert at each x and split off the terminal defect at B. "
                    + "Integrating the nonlocal term over Y ≤ x ≤ X and x ≤ t ≤ B gives "
                    + "K by integrating 1/sqrt(x) from Y to min(t,X). The constant endpoint "
                    + "majorant c is paid over the interval from Y to X."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-window-negative-mass"),
                DeclarationHandle.Create(Module + "negative_mass_le"),
                H("The bound by the weighted negative mass"),
                StatementSource.FromAuthor(Claim(exact: false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write M(k,Y,B) for the integral of "
                    + "(a(t)/sqrt(t)) max(-W(k,t),0) from Y to B and "
                    + "F(Y)=1+2(log(Y)+2)/(log(Y)(1+log(Y))). "
                    + "Use the positive part of -W as the majorant. Its local term can be "
                    + "extended to B, and the kernel K is bounded by (F(Y)-1)a(t)/sqrt(t)."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Function => new Formula.TypeArrow(Real, Real);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula NegativePart(Formula value) => At("max", new Formula.Negate(value), D(0));

    private static Formula Integral(Formula lower, Formula upper, Formula integrand, Formula variable) =>
        Seq(Int, Underscore, Grp(lower), Caret, Grp(upper), Sp, integrand, Sp, F.Id("d"), variable);

    private static Formula Claim(bool exact)
    {
        var k = F.Id("k");
        var g = F.Id("g");
        var y = F.Id("Y");
        var x = F.Id("X");
        var b = F.Id("B");
        var c = F.Id("c");
        var s = F.Id("x");
        var t = F.Id("t");
        var defect = At("E", k, b);
        var lhs = Integral(y, x, new Formula.Fraction(NegativePart(At("Q", k, s)), At("sqrt", s)), s);
        var endpoint = Multiply(Multiply(D(2),
            Seq(Open, Subtract(At("sqrt", x), At("sqrt", y)), Close)),
            exact ? c : NegativePart(defect));
        var mass = exact
            ? Add(Integral(y, x, Multiply(new Formula.Fraction(At("a", t), At("sqrt", t)), At("g", t)), t),
                Integral(y, b, Multiply(At("K", y, x, t), At("g", t)), t))
            : Multiply(At("F", y), At("M", k, y, b));
        var result = Le(lhs, Add(mass, endpoint));
        if (exact)
        {
            var bounds = new Formula.Logic(Le(y, t), FormulaLogicOperator.And, Le(t, b));
            var nonnegative = All("t", Real, Imp(bounds, Le(D(0), At("g", t))));
            var majorant = All("t", Real, Imp(bounds,
                Le(new Formula.Negate(At("W", k, t)), At("g", t))));
            result = Imp(At("IntegrableOn", g, At("Icc", y, b)),
                Imp(nonnegative, Imp(majorant, Imp(Le(D(0), c),
                    Imp(Le(new Formula.Negate(defect), c), result)))));
        }
        result = Imp(Le(D(2), y), Imp(Le(y, x), Imp(Le(x, b),
            Imp(At("IntegrableOn", k, At("Ioi", y)), result))));
        if (exact)
            result = All("c", Real, result);
        result = All("Y", Real, All("X", Real, All("B", Real, result)));
        return Disp(All("k", Function, exact ? All("g", Function, result) : result));
    }
}
