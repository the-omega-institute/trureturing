using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class RobinCenteredChordDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/RobinCenteredChord.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centered Robin chord quadrature",
        H("Signed transfer and two-sided mass approximation"),
        Blocks(
            Paragraph(Text("Write u(t)=t log(t), E(t)=ψ(t)−t, and A(t)=(1+log(t))/(t log(t))². "
                + "Here A is the activation density and R is the Robin ramp. M(a,b) is "
                + "the weighted negative mass of the tail of the Chebyshev kernel E(t)/t².")),
            Describe.Lean(DescribeId.Create("robin-centered-chord-weights"),
                DeclarationHandle.Create(Module + "chord_weight_balance"),
                H("The two chord weights have equal scaled mass"),
                StatementSource.FromAuthor(Balance()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write C(p,a,x)=p(u(x)−u(a))/u(x). The primitive −1/u "
                    + "gives the activation mass of each interval. The chord coordinate "
                    + "identity makes the left and right scaled masses agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-centered-chord-transfer"),
                DeclarationHandle.Create(Module + "ramp_chord_centered"),
                H("Exact signed transfer for every centering constant"),
                StatementSource.FromAuthor(Transfer()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ramp is minus u times the weighted tail. Subtract "
                    + "the neighboring tails to obtain the two local Chebyshev integrals. "
                    + "Equal scaled masses cancel the contribution of the same constant m "
                    + "on the two sides."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-centered-chord-error"),
                DeclarationHandle.Create(Module + "abs_ramp_chord_error_le"),
                H("The Chebyshev range controls the pointwise error"),
                StatementSource.FromAuthor(Error()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Center at the lower bound L. Each scaled integral "
                    + "is between zero and (U−L)C(p,a,x), so their signed difference "
                    + "has absolute value at most (U−L)C(p,a,x)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-centered-chord-coefficient"),
                DeclarationHandle.Create(Module + "chord_weight_coefficient"),
                H("Coordinate coefficient and its uniform bound"),
                StatementSource.FromAuthor(Coefficient()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Solve the chord coordinate identity for p. "
                    + "The product of the two nonnegative gaps in u is at most one "
                    + "quarter of the square of their sum, and u(x)≥u(a)>0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-centered-chord-mass"),
                DeclarationHandle.Create(Module + "abs_mass_sub_chord_le"),
                H("Two-sided bound for the actual weighted negative mass"),
                StatementSource.FromAuthor(Mass()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed a and b put Q(a,b,t)=(u(t)−u(a))/(u(b)−u(a)) "
                    + "and H(a,b,t)=(1−Q(a,b,t))R(a)+Q(a,b,t)R(b). The true mass "
                    + "density is w(t) max(R(t),0), where w(t)=(log(t)/(1+log(t)))/(t sqrt(t)). "
                    + "Taking positive parts contracts the pointwise error. Bound w by "
                    + "1/(a sqrt(a)), bound the coordinate gap by 3(b−a)log(a), and "
                    + "integrate the resulting bound over the cell."))), DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);

    private static Formula Reals(Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; i--)
            body = All(names[i], body);
        return body;
    }

    private static Formula Given(Formula result, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; i--)
            result = new Formula.Logic(hypotheses[i], FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bracket(Formula body) => Seq(Open, body, Close);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula body) => Seq(body, Caret, Grp(D(2)));
    private static Formula Integral(Formula left, Formula right, Formula term) =>
        Seq(Int, Underscore, Grp(left), Caret, Grp(right), Sp, term, Sp, F.Id("d"), F.Id("t"));

    private static Formula Gap(Formula left, Formula right) => Subtract(At("u", right), At("u", left));
    private static Formula Cell(Formula a, Formula x, Formula b) => And(Le(a, x), Le(x, b));
    private static Formula Total(Formula p, Formula q) => Eq(Add(p, q), D(1));
    private static Formula Coordinate(Formula a, Formula b, Formula x, Formula p, Formula q) =>
        Eq(Add(Multiply(p, At("u", a)), Multiply(q, At("u", b))), At("u", x));
    private static Formula ChordError(Formula a, Formula b, Formula x, Formula p, Formula q) =>
        Subtract(Subtract(At("R", x), Multiply(p, At("R", a))), Multiply(q, At("R", b)));

    private static Formula Range(Formula a, Formula b, Formula lower, Formula upper)
    {
        var t = F.Id("t");
        return All("t", Given(And(Le(lower, At("E", t)), Le(At("E", t), upper)), Cell(a, t, b)));
    }

    private static Formula Balance()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var density = At("A", F.Id("t"));
        var common = At("C", p, a, x);
        var left = Multiply(Multiply(p, At("u", a)), Integral(a, x, density));
        var right = Multiply(Multiply(q, At("u", b)), Integral(x, b, density));
        var endpoint = Fraction(Multiply(q, Bracket(Gap(x, b))), At("u", x));
        return Disp(Reals(Given(And(Eq(left, common), And(Eq(right, common), Eq(endpoint, common))),
            Lt(D(1), a), Cell(a, x, b), Total(p, q), Coordinate(a, b, x, p, q)),
            "a", "b", "x", "p", "q"));
    }

    private static Formula Transfer()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var t = F.Id("t");
        var centered = Multiply(Bracket(Subtract(At("E", t), F.Id("m"))), At("A", t));
        var left = Multiply(Multiply(p, At("u", a)), Integral(a, x, centered));
        var right = Multiply(Multiply(q, At("u", b)), Integral(x, b, centered));
        return Disp(Reals(Given(All("m", Eq(ChordError(a, b, x, p, q), Subtract(left, right))),
            Le(D(2), a), Cell(a, x, b), Total(p, q), Coordinate(a, b, x, p, q)),
            "a", "b", "x", "p", "q"));
    }

    private static Formula Error()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var lower = F.Id("L");
        var upper = F.Id("U");
        var width = Bracket(Subtract(upper, lower));
        return Disp(Reals(Given(Le(new Formula.Absolute(ChordError(a, b, x, p, q)),
                Multiply(width, At("C", p, a, x))),
            Le(D(2), a), Cell(a, x, b), Le(D(0), p), Le(D(0), q), Total(p, q),
            Coordinate(a, b, x, p, q), Range(a, b, lower, upper)),
            "a", "b", "x", "p", "q", "L", "U"));
    }

    private static Formula Coefficient()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var common = At("C", p, a, x);
        var ratio = Fraction(Multiply(Bracket(Gap(a, x)), Bracket(Gap(x, b))),
            Multiply(At("u", x), Bracket(Gap(a, b))));
        var bound = Fraction(Gap(a, b), Multiply(D(4), At("u", a)));
        return Disp(Reals(Given(And(Eq(common, ratio), Le(common, bound)),
            Lt(D(1), a), Lt(a, b), Cell(a, x, b), Total(p, q), Coordinate(a, b, x, p, q)),
            "a", "b", "x", "p", "q"));
    }

    private static Formula Mass()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var lower = F.Id("L");
        var upper = F.Id("U");
        var t = F.Id("t");
        var chord = Integral(a, b, Multiply(At("w", t), At("max", At("H", a, b, t), D(0))));
        var budget = Fraction(Multiply(Multiply(D(3), Bracket(Subtract(upper, lower))),
                Square(Bracket(Subtract(b, a)))),
            Multiply(Multiply(D(4), Square(a)), At("sqrt", a)));
        return Disp(Reals(Given(Le(new Formula.Absolute(Subtract(At("M", a, b), chord)), budget),
            Le(At("exp", D(1)), a), Lt(a, b), Le(b, Multiply(D(2), a)), Range(a, b, lower, upper)),
            "a", "b", "L", "U"));
    }
}
