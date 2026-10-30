using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LiMorganSiegristInflectionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/LiMorganSiegristInflectionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/li2026concavity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible polynomial forcing produces two distinct zeros of the second derivative.",
        H("Nonuniqueness of the fractional concavity transition"),
        Blocks(
            Node("rlIntegral", "The fractional integral", IntegralFormula(),
                "Definition 1.1, PDF p. 2: “For α > 0, the left-sided Riemann–Liouville fractional integral of a locally integrable function u is defined by I^α_{a+}u(x) = (1/Γ(α)) ∫_a^x (x − t)^{α−1} u(t) dt, x > a, whenever the integral is finite.” The formula specializes a to zero. Real powers and the interval integral are Lean's Real.rpow and intervalIntegral.integral. Lean defines the integral for all real parameters; its interpretation here uses positive order and positive x.",
                AssessedProvenance.FromLiterature(Source)),
            Node("solution", "The integral representation of the solution", SolutionFormula(),
                "Section 3, equation (7), PDF p. 11: the weak solution “is equivalently represented by u(x) = (I^α_{0+}f)(x) + c x^{α−1}, c = −(I^α_{0+}f)(1), x ∈ [0, 1]. (7) Conversely, the function defined by this formula is the unique weak solution”. The displayed expression substitutes the value of c. The representation defines solution; equivalence with the fractional Sobolev weak formulation is supplied by the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Hypotheses", "The assumptions on the forcing", HypothesesFormula(),
                "Theorem 5.2, PDF p. 27: “Let f ∈ C([0, 1]) ∩ C¹((0, 1]) satisfy f(1) = 0 and f ≥ 0 on [0, 1], with f ≢ 0. Assume, in addition, that lim_{x→0+} x^{(3−α)/(2−α)} f′(x) = 0.” ContinuousOn and ContDiffOn express the two regularity requirements on Set.Icc 0 1 and Set.Ioc 0 1. The right-sided limit uses nhdsWithin 0 (Set.Ioi 0), and deriv f is the derivative occurring in that limit.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 6.1", Disp(Iff(F.Id("claim"), ClaimBody())),
                "Conjecture 6.1, PDF p. 43: “Let 1 < α < 2. Under the hypotheses of Theorem 5.2, the second derivative F″ has exactly one zero in (0, 1). Moreover, F″ changes sign at this zero, so that this point is the unique inflection point of F.” The source adds: “At present, even the uniqueness of the inflection point remains open”. The solution is represented by equation (7); iteratedDeriv 2 is its second derivative. Uniqueness quantifies over all zeros in Set.Ioo 0 1. Sign change means a negative product at every pair of points sufficiently close on opposite sides of the zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Conjecture 6.1 is false", Disp(Seq(Neg, Parenthesized(ClaimBody()))),
                "Take α = 3/2 and f(x) = (1 − x)(1 + 5x¹²). This polynomial satisfies all six assumptions in Hypotheses. Multiplying the second derivative by the positive factor x^(3/2) Γ(3/2) gives the polynomial 180640483/1764461790 + x/2 − x² + (10485760/676039)x¹³ − (4194304/260015)x¹⁴. Its signs at 7/10, 3/4 and 4/5 are positive, negative and positive. Continuity gives one zero in each of the disjoint intervals (7/10, 3/4) and (3/4, 4/5), contradicting uniqueness. This proves nonuniqueness; an exact count of three zeros and simplicity of those zeros are not conclusions of this theorem. The at-least-one conclusion of Theorem 5.2 is compatible with this example, and the principal-eigenfunction Mittag–Leffler zero question is unaffected.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("li-morgan-siegrist-2026-inflection-points-conjecture-6-1"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("li-morgan-siegrist-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(Formula x, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, x, Colon, Sp, Reals(), Sp, Mapsto, Sp, body));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Functions() => new Formula.TypeArrow(Reals(), Reals());
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Second(Formula a, Formula f, Formula x) =>
        Call("iteratedDeriv", D(2), Call("solution", a, f), x);

    private static Formula IntegralFormula()
    {
        Formula a = Alpha, u = F.Id("u"), x = F.Id("x"), t = F.Id("t");
        Formula integrand = Mul(Pow(Parenthesized(Sub(x, t)), Sub(a, D(1))), App(u, t));
        Formula integral = Seq(Int, Underscore, Grp(D(0)), Caret, Grp(x), Sp,
            integrand, Sp, F.Id("d"), t);
        Formula rhs = Mul(Pow(Call("Real.Gamma", a), Seq(Minus, D(1))), integral);
        return Disp(All(a, Reals(), All(u, Functions(), All(x, Reals(),
            Equal(Call("rlIntegral", a, u, x), rhs)))));
    }

    private static Formula SolutionFormula()
    {
        Formula a = Alpha, f = F.Id("f"), x = F.Id("x");
        Formula rhs = Sub(Call("rlIntegral", a, f, x),
            Mul(Call("rlIntegral", a, f, D(1)), Pow(x, Sub(a, D(1)))));
        return Disp(All(a, Reals(), All(f, Functions(), All(x, Reals(),
            Equal(Call("solution", a, f, x), rhs)))));
    }

    private static Formula HypothesesFormula()
    {
        Formula a = Alpha, f = F.Id("f"), x = F.Id("x");
        Formula nonnegative = All(x, Reals(), Arrow(Member(x, Call("Set.Icc", D(0), D(1))),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, App(f, x))));
        Formula nonzero = Some(x, Reals(), And(Member(x, Call("Set.Icc", D(0), D(1))),
            new Formula.Relation(App(f, x), FormulaRelationOperator.NotEqual, D(0))));
        Formula exponent = new Formula.Fraction(Sub(D(3), a), Sub(D(2), a));
        Formula limit = Call("Tendsto", Lam(x, Mul(Pow(x, exponent), Call("deriv", f, x))),
            Call("nhdsWithin", D(0), Call("Set.Ioi", D(0))), Call("nhds", D(0)));
        Formula body = And(Call("ContinuousOn", f, Call("Set.Icc", D(0), D(1))),
            And(Call("ContDiffOn", Reals(), D(1), f, Call("Set.Ioc", D(0), D(1))),
                And(Equal(App(f, D(1)), D(0)), And(nonnegative, And(nonzero, limit)))));
        return Disp(All(a, Reals(), All(f, Functions(), Iff(Call("Hypotheses", a, f), body))));
    }

    private static Formula ClaimBody()
    {
        Formula a = Alpha, f = F.Id("f"), xi = Xi, eta = F.Id("eta"), delta = DeltaLower,
            y = F.Id("y"), z = F.Id("z");
        Formula unique = All(eta, Reals(), Arrow(Member(eta, Call("Set.Ioo", D(0), D(1))),
            Arrow(Equal(Second(a, f, eta), D(0)), Equal(eta, xi))));
        Formula opposite = Less(Mul(Second(a, f, y), Second(a, f, z)), D(0));
        Formula signs = Some(delta, Reals(), And(Less(D(0), delta), All(y, Reals(), All(z, Reals(),
            Arrow(Less(Sub(xi, delta), y), Arrow(Less(y, xi), Arrow(Less(xi, z),
                Arrow(Less(z, new Formula.Binary(xi, FormulaBinaryOperator.Add, delta)), opposite))))))));
        Formula zero = Some(xi, Reals(), And(Member(xi, Call("Set.Ioo", D(0), D(1))),
            And(Equal(Second(a, f, xi), D(0)), And(unique, signs))));
        return All(a, Reals(), Arrow(Less(D(1), a), Arrow(Less(a, D(2)),
            All(f, Functions(), Arrow(Call("Hypotheses", a, f), zero)))));
    }
}
