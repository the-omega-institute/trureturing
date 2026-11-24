using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinWindowMassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robin window mass and the Riemann hypothesis",
        H("The Robin budget on an outer power window"),
        Blocks(
            Paragraph(Text("Take k(t)=(ψ(t)-t)/t² in the weighted-tail estimate. Write q(x) "
                + "for the tail of (θ(t)-t)/t², M(Y,B) for the weighted negative mass "
                + "of k, and E(B) for its endpoint defect. The Robin budget is "
                + "R(Y,b)=M(Y,Yᵇ)+sqrt(Y) max(-E(Yᵇ),0). The endpoint defect is "
                + "evaluated at the right endpoint and multiplied by the square root "
                + "of the left endpoint.")),
            Describe.Lean(DescribeId.Create("robin-inner-window-upper-bound"),
                DeclarationHandle.Create(Module + "prime_mass_le_power"),
                H("Prime mass on the inner power window"),
                StatementSource.FromAuthor(Upper()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The correction from ψ to θ costs at most "
                    + "2C(d-1)log(Y). On the inner window the endpoint length in the "
                    + "square-root variable is at most Y^((d-1)/2)sqrt(Y), "
                    + "and the coefficient of the weighted negative mass is at most 4."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-off-line-growth"),
                DeclarationHandle.Create(Module + "off_line_zero_forces_robin_budget"),
                H("A lower bound on every sufficiently late outer window"),
                StatementSource.FromAuthor(Growth()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a zero with real part β in (1/2,1), choose "
                    + "one inner exponent d strictly between 1 and b and sufficiently close to 1. "
                    + "The prime-tail lower bound on the inner window has exponent d(β-1/2)-δ. "
                    + "This positive power absorbs the logarithmic correction. After subtracting "
                    + "the transport loss (d-1)/2 and absorbing the fixed factor, the exponent "
                    + "β-1/2-ε remains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-small-windows-imply-rh"),
                DeclarationHandle.Create(Module + "rh_of_frequently_small_robin_windows"),
                H("Arbitrarily late small Robin windows imply RH"),
                StatementSource.FromAuthor(Criterion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive η it suffices to have arbitrarily "
                    + "late windows on which the joint budget is at most Y^η. A right-half-strip "
                    + "zero would contradict this for η=(β-1/2)/3. The right-half-strip "
                    + "reduction then gives the Riemann hypothesis."))), DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Half => new Formula.Fraction(D(1), D(2));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);

    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula Power(Formula x, Formula y) => Seq(x, Caret, Grp(y));

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Upper()
    {
        var y = F.Id("Y");
        var d = F.Id("d");
        var b = F.Id("b");
        var c = F.Id("C");
        var t = F.Id("t");
        var x = F.Id("x");
        var density = new Formula.Fraction(At("max", new Formula.Negate(At("q", x)), D(0)), At("sqrt", x));
        var mass = Seq(Int, Underscore, Grp(y), Caret, Grp(Power(y, d)), Sp, density, Sp, F.Id("d"), x);
        var width = Seq(Open, Subtract(d, D(1)), Close);
        var budget = Multiply(Multiply(D(4), Power(y, new Formula.Fraction(Subtract(d, D(1)), D(2)))),
            At("R", y, b));
        var correction = Multiply(Multiply(Multiply(D(2), c), width), At("log", y));
        var powers = All("t", Real, Imp(Le(D(1), t),
            Le(Subtract(At("psi", t), At("theta", t)), Multiply(c, At("sqrt", t)))));
        var premises = Imp(Le(At("exp", D(1)), y),
            Imp(Le(D(1), d), Imp(Le(d, b), Imp(powers, Le(mass, Add(budget, correction))))));
        return Disp(All("C", Real, All("Y", Real, All("d", Real, All("b", Real, premises)))));
    }

    private static Formula Growth()
    {
        var z = F.Id("z");
        var beta = At("Re", z);
        var b = F.Id("b");
        var e = F.Id("e");
        var y = F.Id("Y");
        var t = F.Id("T");
        var zero = new Formula.Relation(At("zeta", z), FormulaRelationOperator.Equal, D(0));
        var bound = Le(Power(y, Subtract(Subtract(beta, Half), e)), At("R", y, b));
        var tail = Exists("T", All("Y", Real, Imp(Le(t, y), bound)));
        var windows = All("b", Real, All("e", Real, Imp(Lt(D(1), b), Imp(Lt(D(0), e), tail))));
        return Disp(All("z", Complex, Imp(zero, Imp(Lt(Half, beta), Imp(Lt(beta, D(1)), windows)))));
    }

    private static Formula Criterion()
    {
        var b = F.Id("b");
        var e = F.Id("e");
        var y = F.Id("Y");
        var t = F.Id("T");
        var late = All("T", Real, Exists("Y", And(Le(t, y), Le(At("R", y, b), Power(y, e)))));
        var small = All("e", Real, Imp(Lt(D(0), e), late));
        return Disp(All("b", Real, Imp(Lt(D(1), b), Imp(small, F.Id("RiemannHypothesis")))));
    }
}
