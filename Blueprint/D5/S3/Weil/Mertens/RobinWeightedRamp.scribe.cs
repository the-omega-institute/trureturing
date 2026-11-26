using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class RobinWeightedRampDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/RobinWeightedRamp.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robin weighted-ramp quadrature",
        H("Finite Mangoldt ramps and endpoint bounds"),
        Blocks(
            Paragraph(Text("Write u(x)=x log(x) and k(t)=(ψ(t)−t)/t². The Robin ramp is "
                + "R(x)=u(x)E₂Λ(x)−(ψ(x)−x), where E₂Λ is the centered weighted Mangoldt sum. "
                + "W(x) is the weighted tail of k, M(c,d) is its weighted negative mass "
                + "on [c,d], and S(x)=max(R(x),0). The constant γ is Euler's constant, "
                + "and floor denotes the natural floor.")),
            Describe.Lean(DescribeId.Create("robin-ramp-weighted-tail"),
                DeclarationHandle.Create(Module + "ramp_eq_neg_weightedTail"),
                H("The weighted-tail identity"),
                StatementSource.FromAuthor(Tail()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the complete Mertens ledger by u(x) "
                    + "and cancel the Chebyshev endpoint term."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-finite-mangoldt-ramps"),
                DeclarationHandle.Create(Module + "ramp_eq_sum"),
                H("The exact finite ramp sum"),
                StatementSource.FromAuthor(RampSum()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ramp at an integer n contributes only for x greater than n. "
                    + "Monotonicity of u on this range permits a common cutoff N at or above "
                    + "the natural floor of x. The endpoint ramp vanishes when x=n."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-ramp-upper-chord"),
                DeclarationHandle.Create(Module + "ramp_chord"),
                H("An upper chord in the x log x coordinate"),
                StatementSource.FromAuthor(Chord()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ramp in the common finite sum is a nonnegative "
                    + "Mangoldt weight times the positive part of an affine function of u. "
                    + "The smooth centering term has a tangent remainder between zero and "
                    + "3(z−a)²/a for a ≤ z ≤ 2a and a ≥ exp(1). The affine tangent "
                    + "cancels in the chord difference."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-cell-negative-mass"),
                DeclarationHandle.Create(Module + "mass_le_of_cell"),
                H("Endpoint samples bound the mass of a subinterval"),
                StatementSource.FromAuthor(Cell()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weighted negative-mass density is "
                    + "(log(x)/(1+log(x))) S(x)/(x sqrt(x)). Bound the first factor by one, "
                    + "bound S(x) by the endpoint samples and chord allowance, then integrate "
                    + "the resulting constant bound over [c,d]."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-quartic-negative-mass"),
                DeclarationHandle.Create(Module + "quartic_mass_le"),
                H("Fourth-power cells with curvature allowance 675"),
                StatementSource.FromAuthor(Quartic()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n ≥ 6 the fourth-power cell has width at most 15n³ "
                    + "and its right endpoint is at most twice the left endpoint. With "
                    + "a=n⁴ the chord allowance is at most 675n² and a sqrt(a)=n⁶. "
                    + "The subinterval length therefore multiplies the normalized samples "
                    + "and allowance by (d−c)/n⁴."))), DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Reals(Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; i--)
            body = All(names[i], Real, body);
        return body;
    }

    private static Formula Given(Formula result, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; i--)
            result = new Formula.Logic(hypotheses[i], FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Fraction(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Parens(Formula x) => Seq(Open, x, Close);
    private static Formula Pow(Formula x, byte n) => Seq(x, Caret, Grp(D(n)));
    private static Formula Curvature(Formula a, Formula b) =>
        Fraction(Multiply(D(3), Pow(Parens(Subtract(b, a)), 2)), a);

    private static Formula Tail()
    {
        var x = F.Id("x");
        return Disp(Reals(Given(Eq(At("R", x), Multiply(new Formula.Negate(At("u", x)), At("W", x))),
            Le(D(2), x)), "x"));
    }

    private static Formula RampSum()
    {
        var x = F.Id("x");
        var n = F.Id("n");
        var cutoff = F.Id("N");
        var coordinate = At("u", x);
        var term = Multiply(At("Lambda", n), At("max", Subtract(Fraction(coordinate, At("u", n)), D(1)), D(0)));
        var sum = Seq(Sum, Underscore, Grp(And(Le(D(2), n), Le(n, cutoff))), Sp, term);
        var center = Multiply(coordinate, Parens(Add(At("log", At("log", x)), F.Id("gamma"))));
        return Disp(Reals(All("N", Nat, Given(Eq(At("R", x), Add(Subtract(sum, center), x)),
            Le(D(2), x), Le(At("floor", x), cutoff))), "x"));
    }

    private static Formula Chord()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var bound = Add(Add(Multiply(p, At("R", a)), Multiply(q, At("R", b))), Curvature(a, b));
        return Disp(Reals(Given(Le(At("R", x), bound),
            Le(At("exp", D(1)), a), Lt(a, b), Le(b, Multiply(D(2), a)),
            And(Le(a, x), Le(x, b)), Le(D(0), p), Le(D(0), q), Eq(Add(p, q), D(1)),
            Eq(Add(Multiply(p, At("u", a)), Multiply(q, At("u", b))), At("u", x))),
            "a", "b", "x", "p", "q"));
    }

    private static Formula Cell()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var d = F.Id("d");
        var width = Fraction(Subtract(d, c), Multiply(a, At("sqrt", a)));
        var samples = Add(At("S", a), At("S", b));
        var bound = Multiply(width, Parens(Add(samples, Curvature(a, b))));
        return Disp(Reals(Given(Le(At("M", c, d), bound),
            Le(At("exp", D(1)), a), Lt(a, b), Le(b, Multiply(D(2), a)),
            Le(a, c), Le(c, d), Le(d, b)), "a", "b", "c", "d"));
    }

    private static Formula Quartic()
    {
        var n = F.Id("n");
        var c = F.Id("c");
        var d = F.Id("d");
        var left = Pow(n, 4);
        var right = Pow(Parens(Add(n, D(1))), 4);
        var samples = Fraction(Add(At("S", left), At("S", right)), Pow(n, 2));
        var bound = Multiply(Fraction(Subtract(d, c), left), Parens(Add(samples, D(6, 7, 5))));
        return Disp(All("n", Nat, Given(Reals(Given(Le(At("M", c, d), bound),
            Le(left, c), Le(c, d), Le(d, right)), "c", "d"), Le(D(6), n))));
    }
}
