using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.QGammaTuran;

internal sealed class FunctionResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2018qgamma");
    private const string Prefix = "D5/S3/Analytic/QGammaTuran/FunctionResult.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent reciprocal q-gamma series whose function Turanian is negative.",
        H("The function clause of Conjecture 1 is false"), Blocks(
            Node("qprod_multipliable", QHyp(All("a", R, Call("Multipliable", Lambda("j", Sub(D(1), Mul(V("a"), Pow(V("q"), V("j")))))))), "Geometric summability makes the q-product multipliable."),
            Node("qprod_step", QHyp(All("a", R, Eqn(P(V("a")), Mul(Sub(D(1), V("a")), P(Mul(V("a"), V("q"))))))), "Removing the first product factor shifts its parameter by q."),
            Node("qprod_nonneg", QA(false, Leq(D(0), P(V("a")))), "Nonnegative product factors give a nonnegative infinite product."),
            Node("qprod_ne_zero", QA(true, new Formula.Not(Eqn(P(V("a")), D(0)))), "Strictly positive factors and geometric convergence exclude a zero product."),
            Node("qprod_pos", QA(true, Positive(P(V("a")))), "The infinite product is positive for a in the half-open unit interval."),
            Node("qprod_le_one", QA(false, Leq(P(V("a")), D(1))), "Products of factors in the unit interval are at most one."),
            Node("qprod_lower", QA(false, Leq(Sub(D(1), new Formula.Fraction(V("a"), Sub(D(1), V("q")))), P(V("a")))), "The geometric sum bounds the loss of the product from one."),
            Node("qprod_split", QHyp(All("a", R, All("n", N, Eqn(P(V("a")), Mul(FiniteP(), P(Mul(V("a"), Pow(V("q"), V("n"))))))))), "A finite prefix times the remaining infinite product equals the full product."),
            Node("qprod_bounds", QA(false, All("n", N, Both(Leq(Mul(FiniteP(), Sub(D(1), new Formula.Fraction(Mul(V("a"), Pow(V("q"), V("n"))), Sub(D(1), V("q"))))), P(V("a"))), Leq(P(V("a")), FiniteP())))), "A finite prefix gives both bounds, using the geometric tail loss for the lower bound."),
            Node("rqgamma_eq", All("q", R, Imp(Positive(V("q")), All("x", R, Eqn(RG(V("x")), new Formula.Fraction(P(Pow(V("q"), V("x"))), Mul(P(V("q")), Pow(Sub(D(1), V("q")), Sub(D(1), V("x"))))))))), "The reciprocal q-gamma definition in q-Pochhammer notation."),
            Node("qseries", BindR("q mu x", All("g", new Formula.TypeArrow(N, R),
                Eqn(QS(V("mu"), V("x"), V("g")), InfiniteSum("n", Term(V("mu"), V("x"), V("g")))))),
                "Theorem 3, printed page 11 of arXiv:1702.03788v1: “For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define g(µ; x) = ∑ₙ₌₀∞ gₙxⁿ/Γq(µ + n). (16)” The reciprocal is the infinite-product rqgamma of Result. Equation (6), printed page 4: “The q-gamma function is defined by Γq(z) = (1 − q)^(1−z) (q; q)∞/(q^z; q)∞ (6) for |q| < 1 and all complex z such that q^(z+k) ≠ 1 for k ∈ N₀.” At nonpositive integers the reciprocal extension is zero.", DescribeRole.Definition, true),
            Node("radius", BindR("q mu", All("g", new Formula.TypeArrow(N, R),
                Eqn(Radius(V("mu"), V("g")), Call("FormalMultilinearSeries.radius",
                    Call("FormalMultilinearSeries.ofScalars", R, Lambda("n",
                        Mul(new Formula.Apply(Parenthesized(V("g")), [V("n")]), RG(Add(V("mu"), V("n")))))))))),
                "Rg is the radius of series (16) at the given µ, with coefficients gₙ rqgamma(q,µ+n). It takes values in the extended nonnegative reals. The standard scalar formal power series has coefficient norms |gₙ rqgamma(q,µ+n)|. Its Mathlib radius is the supremum of nonnegative radii at which these norms times the corresponding powers are bounded; equivalently it is the supremum of radii of absolute summability. Printed page 12: “Writing Rg > 0 for the radius of convergence in (16), we claim that the next conjecture is true.”", DescribeRole.Definition, true),
            Node("claim", Eqn(V("claim"), ClaimBody()),
                "Theorem 3, printed page 11: “Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian ∆g(α, β; x) = g(µ + α; x)g(µ + β; x) − g(µ; x)g(µ + α + β; x) is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then ∆g(α, β; x) has positive power series coefficients at all powers of x.” Conjecture 1, printed page 12: “All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.” The function clause quantifies over 0<x<Rg, where radius(q,µ,g) is the radius of (16) at the given µ. It has no α≤β+1 restriction. AdmissibleSeq is the nontrivial, nonnegative, log-concave sequence condition with no internal zeros; admissible_one supplies gₙ=1.", DescribeRole.Definition, true),
            Node("hsum", BindR("q a y", Eqn(HS(V("a")), InfiniteSum("n", Hterm()))),
                "The normalized series is expressed with a=q^s and y=x(1−q). This form includes the pole at s=0 without division by a vanishing q-number.", DescribeRole.Definition),
            Node("plower", BindR("q a", All("N", N, Eqn(Call("plower", V("q"), V("a"), V("N")),
                Mul(PrefixProduct(), Sub(D(1), Div(Mul(V("a"), Pow(V("q"), V("N"))), Sub(D(1), V("q")))))))),
                "A finite q-product multiplied by the lower bound on its remaining factors.", DescribeRole.Definition),
            Node("pupper", BindR("q a", All("N", N, Eqn(Call("pupper", V("q"), V("a"), V("N")), PrefixProduct()))),
                "The finite product bounds the full product from above.", DescribeRole.Definition),
            Node("hsummable", QAY(false, Call("Summable", Lambda("n", Hterm()))),
                "When a and y lie in the unit interval, normalized terms are nonnegative and bounded by yⁿ. The geometric series proves summability."),
            Node("hshift", QAY(true, Eqn(HS(V("a")), Add(P(V("a")), Mul(V("y"), HS(Mul(V("a"), V("q"))))))),
                "Separating the first term shifts a to aq. This identity also applies when a exceeds one but aq does not."),
            Node("hbounds", QAY(false, All("K", N, All("N", N, Both(
                Leq(SumK(Mul(Pow(V("y"), V("n")), Call("plower", V("q"), Mul(V("a"), Pow(V("q"), V("n"))), V("N")))), HS(V("a"))),
                Leq(HS(V("a")), Add(SumK(Mul(Pow(V("y"), V("n")), Call("pupper", V("q"), Mul(V("a"), Pow(V("q"), V("n"))), V("N")))), Div(Pow(V("y"), V("K")), Sub(D(1), V("y"))))))))),
                "qprod_bounds bounds each product in a finite prefix. Summable.sum_le_tsum supplies the lower bound; the omitted normalized terms are at most a geometric tail y^K/(1−y)."),
            Node("normalizedTerm", QPositive(BindR("s x", All("n", N, Eqn(
                Mul(Pow(V("x"), V("n")), RG(Add(V("s"), V("n")))),
                Div(Mul(Pow(Mul(V("x"), Sub(D(1), V("q"))), V("n")), P(Mul(Pow(V("q"), V("s")), Pow(V("q"), V("n"))))), Den(V("s"))))))),
                "rqgamma_eq and the real power addition law normalize each term. The denominator is independent of n."),
            Node("series_eq", QPositive(BindR("s x", Eqn(QS(V("s"), V("x"), One()),
                Div(Call("hsum", V("q"), Pow(V("q"), V("s")), Mul(V("x"), Sub(D(1), V("q")))), Den(V("s")))))),
                "Taking the infinite sum gives the normalized expression for the constant-sequence q-gamma series."),
            Node("hsummable_any", QAY(true, Call("Summable", Lambda("n", Hterm()))),
                "The first term may have either sign. After removing it, aq≤1 permits geometric domination."),
            Node("series_summable", QPositive(BindR("s x", Imp(Leq(Mul(Pow(V("q"), V("s")), V("q")), D(1)),
                Imp(Leq(D(0), Mul(V("x"), Sub(D(1), V("q")))), Imp(Less(Mul(V("x"), Sub(D(1), V("q"))), D(1)),
                    Call("Summable", Lambda("n", Term(V("s"), V("x"), One())))))))),
                "The normalized geometric comparison proves summability of the original real q-gamma series, hence absolute summability. It applies to all four shifts at the example."),
            Node("r", Eqn(V("r"), Rat(93, 100)), "The rational base.", DescribeRole.Definition),
            Node("q", Eqn(V("q"), Pow(V("r"), new Formula.Number(10))), "The q parameter.", DescribeRole.Definition),
            Node("y", Eqn(V("y"), Mul(V("r"), Sub(D(1), V("q")))), "The normalized series variable at x=r.", DescribeRole.Definition),
            Node("qpos", Positive(V("q")), "The example has positive q."),
            Node("qlt", Less(V("q"), D(1)), "The example has q less than one."),
            Node("ypos", Leq(D(0), V("y")), "The normalized series variable is nonnegative."),
            Node("ylt", Less(V("y"), D(1)), "The example lies strictly in the geometric convergence disk."),
            Node("numH3", Interval(621758, 627611, 1000000, HS(Pow(V("r"), D(3)))), "Ten series terms and six factors enclose the normalized value at s=3/10."),
            Node("numH6", Interval(779999, 786930, 1000000, HS(Pow(V("r"), D(6)))), "Ten series terms and six factors enclose the normalized value at s=6/10."),
            Node("numH10", Interval(986336, 993832, 1000000, HS(Pow(V("r"), new Formula.Number(10)))), "Ten series terms and six factors enclose the normalized value at s=1."),
            Node("numP3", Interval(80786, 82438, 1000000, P(Pow(V("r"), D(3)))), "Six factors enclose the product with parameter r³."),
            Node("numP6", Interval(177796, 180709, 1000000, P(Pow(V("r"), D(6)))), "Six factors enclose the product with parameter r⁶."),
            Node("qpower", All("n", N, Eqn(Pow(V("q"), Div(V("n"), new Formula.Number(10))), Pow(V("r"), V("n")))), "The required fractional powers of q are rational powers of r."),
            Node("series_product", QPositive(BindR("s t x", Eqn(
                Mul(QS(V("s"), V("x"), One()), QS(V("t"), V("x"), One())),
                Div(Mul(Call("hsum", V("q"), Pow(V("q"), V("s")), Mul(V("x"), Sub(D(1), V("q")))),
                    Call("hsum", V("q"), Pow(V("q"), V("t")), Mul(V("x"), Sub(D(1), V("q"))))),
                    Mul(Pow(P(V("q")), D(2)), Pow(Sub(D(1), V("q")), Sub(Sub(D(2), V("s")), V("t")))))))),
                "Products with the same sum of shifts have the same positive normalization denominator."),
            Node("negative_bounds", Both(Leq(D(0), HS(Inv(Pow(V("r"), D(4))))),
                Both(Leq(HS(Inv(Pow(V("r"), D(4)))), Rat(317763, 1000000)),
                Both(Leq(Rat(243809, 1000000), HS(Inv(Pow(V("r"), D(7))))),
                Interval(0, 476937, 1000000, HS(D(1)))))),
                "The first-factor product equation and hshift transfer positive-parameter estimates to s=−2/5 and s=−7/10. At s=0 the product's zero makes hsum(q,1,y)=y hsum(q,q,y)."),
            Node("witness_negative", Less(WitnessDelta(), D(0)),
                "At gₙ=1, q=(93/100)^10 and x=93/100, the product of normalized values at −2/5 and zero is at most 0.151552931931. The product at −7/10 and 3/10 is at least 0.151590196222. Their common normalization denominator is positive, so the original Turanian is strictly negative."),
            Node("witness_radius", Less(Call("ENNReal.ofReal", V("r")), Radius(Rat(-7, 10), One())),
                "At µ=−7/10 and gₙ=1, series_summable gives absolute convergence at x=3/2, since (3/2)(1−q)<1. FormalMultilinearSeries.le_radius_of_summable gives 3/2≤Rg. As 93/100<3/2, the negative Turanian occurs strictly inside the disk of convergence of (16)."),
            Describe.Lean(DescribeId.Create("function-clause-refuted"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the function clause"), StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Take gₙ=1, µ=−7/10, α=3/10, β=7/10, q=(93/100)^10 and x=93/100. The shifts satisfy µ=max(−β,−1), and witness_radius proves 0<x<Rg for the radius of (16) at µ. The strictly negative function value contradicts the universal strict positivity assertion. The proof reuses Result.qprod and Result.rqgamma (definitions), Defs.admissible_one, and JordanCototientRecordLimitInfinity.one_sub_prod_le_sum. Here Defs is D5.S3.Analytic.ReciprocalGammaTuran.Defs and JordanCototientRecordLimitInfinity is D5.S3.Factorization.JordanCototientRecordLimitInfinity. FunctionResult’s private helpers derive the product estimates and reciprocal-product identity from these declarations and pinned Mathlib. Consequence in prose of witness_negative: at this q,x and gₙ=1, log-concavity on an interval containing [−7/10,3/10] is impossible. Indeed, −2/5=(7/10)(−7/10)+(3/10)(3/10) and 0=(3/10)(−7/10)+(7/10)(3/10), with respective right-endpoint weights 3/10 and 7/10. Multiplying the two log-concavity inequalities would give g(−2/5;x)g(0;x) ≥ g(−7/10;x)g(3/10;x), contradicting the proved strict reverse inequality. The endpoint values are strictly positive by the normalized lower bounds and positive denominators. This consequence is not a separate Lean theorem. Log-concavity restricted to nonnegative parameters µ remains OPEN. The integer-shift theorem is outside the example’s parameter choice."))),
                DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-2018-qgamma-turanian-function"), ResolutionKind.Refuted)))));

    private static DocumentBlock.Describe Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create("function-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name.Replace("_", " ")), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula QHyp(Formula body) => All("q", R, Imp(Leq(D(0), V("q")), Imp(Less(V("q"), D(1)), body)));
    private static Formula QA(bool strict, Formula body) => QHyp(All("a", R, Imp(Leq(D(0), V("a")), Imp(strict ? Less(V("a"), D(1)) : Leq(V("a"), D(1)), body))));
    private static Formula FiniteP() => Finite("prod", "j", V("n"), Sub(D(1), Mul(V("a"), Pow(V("q"), V("j")))));
    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")), Sp);
    private static Formula R => Seq(Mathbb, Grp(V("R")), Sp);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Grp([.. parts]), Sp), [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula BindR(string names, Formula body)
    {
        var ns = names.Split(' ');
        for (var i = ns.Length - 1; i >= 0; i--) body = All(ns[i], R, body);
        return body;
    }
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Positive(Formula a) => Less(D(0), a);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Rat(int a, int b) => Div(a < 0 ? new Formula.Negate(new Formula.Number(-a)) : new Formula.Number(a), new Formula.Number(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Inv(Formula a) => Pow(a, new Formula.Negate(D(1)));
    private static Formula Lambda(string n, Formula body) => Seq(Open, V(n), Colon, Sp, N, Close, Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula One() => Lambda("n", D(1));
    private static Formula InfiniteSum(string n, Formula body) => Seq(new Formula.Subscript(Seq(Sum, Apos), Seq(V(n), Colon, Sp, N)), Sp, Parenthesized(body));
    private static Formula Finite(string op, string n, Formula bound, Formula body) => Seq(new Formula.Subscript(op == "sum" ? Sum : Prod, Seq(V(n), InMacro, Sp, Call("Finset.range", bound))), Sp, Parenthesized(body));
    private static Formula SumK(Formula body) => Finite("sum", "n", V("K"), body);
    private static Formula P(Formula a) => Call("Result.qprod", V("q"), a);
    private static Formula RG(Formula s) => Call("Result.rqgamma", V("q"), s);
    private static Formula HS(Formula a) => Call("hsum", V("q"), a, V("y"));
    private static Formula Hterm() => Mul(Pow(V("y"), V("n")), P(Mul(V("a"), Pow(V("q"), V("n")))));
    private static Formula Den(Formula s) => Mul(P(V("q")), Pow(Sub(D(1), V("q")), Sub(D(1), s)));
    private static Formula PrefixProduct() => Finite("prod", "j", V("N"), Sub(D(1), Mul(V("a"), Pow(V("q"), V("j")))));
    private static Formula QS(Formula s, Formula x, Formula g) => Call("qseries", V("q"), s, x, g);
    private static Formula Term(Formula s, Formula x, Formula g) => Mul(Mul(new Formula.Apply(Parenthesized(g), [V("n")]), Pow(x, V("n"))), RG(Add(s, V("n"))));
    private static Formula Radius(Formula s, Formula g) => Call("radius", V("q"), s, g);
    private static Formula Interval(int lo, int hi, int d, Formula v) => Both(Leq(Rat(lo, d), v), Leq(v, Rat(hi, d)));
    private static Formula QPositive(Formula body) => All("q", R, Imp(Positive(V("q")), Imp(Less(V("q"), D(1)), body)));
    private static Formula QAY(bool shifted, Formula body) => BindR("q a y", Imp(Leq(D(0), V("q")), Imp(Less(V("q"), D(1)),
        Imp(Leq(D(0), V("a")), Imp(Leq(shifted ? Mul(V("a"), V("q")) : V("a"), D(1)),
        Imp(Leq(D(0), V("y")), Imp(Less(V("y"), D(1)), body)))))));
    private static Formula WitnessDelta() => Sub(Mul(QS(Rat(-2, 5), V("r"), One()), QS(D(0), V("r"), One())), Mul(QS(Rat(-7, 10), V("r"), One()), QS(Rat(3, 10), V("r"), One())));
    private static Formula ClaimBody() => QPositive(All("g", new Formula.TypeArrow(N, R),
        Imp(Call("D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq", V("g")), BindR("mu alpha beta", Imp(Positive(V("alpha")), Imp(Positive(V("beta")),
        Imp(Leq(Call("max", new Formula.Negate(V("beta")), new Formula.Negate(D(1))), V("mu")), All("x", R, Imp(Positive(V("x")),
        Imp(Less(Call("ENNReal.ofReal", V("x")), Radius(V("mu"), V("g"))), Positive(Sub(
            Mul(QS(Add(V("mu"), V("alpha")), V("x"), V("g")), QS(Add(V("mu"), V("beta")), V("x"), V("g"))),
            Mul(QS(V("mu"), V("x"), V("g")), QS(Add(Add(V("mu"), V("alpha")), V("beta")), V("x"), V("g")))))))))))))));
}
