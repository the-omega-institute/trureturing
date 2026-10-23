using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Chebyshev;

internal sealed class SnakeChebyshevExpansionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/kryvonos2023openproblems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even convex majorant has a degree-six snake with a negative Chebyshev coefficient.",
        H("Nikolov Snake Polynomial Chebyshev Expansion Refutation"),
        Blocks(
            SourceQuotation(),
            Entry("snake", "IsSnake", "Bound and alternating contacts", Snake(),
                "The formal encoding of the quoted characterization uses a real polynomial of degree at most n, "
                + "a pointwise bound on I=[−1,1], and a strictly decreasing map τ from Fin(n+1) to ℝ. "
                + "Its first contact is at most one, its last at least minus one, and its values alternate "
                + "as ω(τᵢ)=(−1)ⁱμ(τᵢ). These conditions express (a) and (b) in the positive initial orientation. "
                + "Uniqueness up to orientation is asserted by the source and is not formalized here.",
                DescribeRole.Definition, true),
            Entry("expansion-claim", "claim", "Nonnegative Chebyshev expansion", Claim(),
                "The formal claim quantifies over every real function continuous, nonnegative, even and convex "
                + "on I, every natural n and every polynomial satisfying IsSnake. It requires a coefficient "
                + "function a:ℕ→ℝ nonnegative at every index, with ω=∑ₖ₌₀ⁿ C(aₖ)Tₖ. "
                + "Tₖ is Chebyshev.T ℝ (k:ℤ), the first-kind polynomial, and C embeds a real constant. "
                + "UP24, arXiv:2504.04845, §7, repeats the assertion as Conjecture 7.1 (Geno Nikolov).",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "A negative constant Chebyshev coefficient", Disp(Seq(Neg, Sp, V("claim"))),
                "Take n=6, μ(x)=max{1,(4860|x|−1078)/137}, and "
                + "P(x)=(38656x⁶−41568x⁴+6831x²−137)/137. The majorant is positive, continuous, even and convex. "
                + "On [0,1/4], factorizations of 137(1−P) and 137(1+P) prove |P|≤1. "
                + "On [1/4,1], with L(x)=(4860x−1078)/137, the factors of 137(L−P) are "
                + "(1−x)(4x−1)(9664x⁴+12080x³+2292x²−155x+941), and "
                + "137(L+P)=(4x−3)²(2416x⁴+3624x³+1479x²+180x−135). "
                + "The last quartic equals 137/2+(x−1/4)(2416x³+4228x²+2536x+814). "
                + "The interval factors are nonnegative; evenness extends the bound to [−1,1]. "
                + "The contacts 1,3/4,1/4,0,−1/4,−3/4,−1 have values "
                + "3782/137,−2567/137,1,−1,1,−2567/137,3782/137, respectively. "
                + "The private lemmas P_bound_small, P_bound_large and P_snake establish these snake conditions. "
                + "Comparing the coefficients of x⁰,x²,x⁴,x⁶ in a representation by T₀,…,T₆ forces "
                + "a₀=−459/274, as proved by constant_coefficient_negative. "
                + "The exact polynomial expansion is P=(−459/274)T₀+(1503/274)T₂+(2052/137)T₄+(1208/137)T₆. "
                + "Thus nonnegative coefficients are impossible. Nikolov–Shadrin, arXiv:1210.7795, "
                + "uses positive expansion as a sufficient hypothesis for extremality in majorant inequalities. "
                + "This refutation leaves the folklore Markov-extremality conjecture and UP24 Problem 7.1 open; "
                + "it also leaves strictly convex or smoother majorants and degrees at most five unsettled. "
                + "Literature coverage is limited to the cited arXiv versions.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("nikolov-2023-snake-polynomial-chebyshev-expansion"),
                ResolutionKind.Refuted) : null);

    private static DocumentBlock SourceQuotation() => Paragraph(
        Text("Kryvonos (ed.), arXiv:2312.07754v1, section “Snake polynomials with positive Chebyshev expansions”, definition verbatim: "
            + "“Consider a majorant µ ∈ C[−1, 1], µ(x) ≥ 0, x ∈ [−1, 1]. If there exists P ∈ Pn, P ≠ 0, "
            + "such that −µ(x) ≤ P(x) ≤ µ(x), x ∈ [−1, 1], then there exists a unique (up to orientation) "
            + "polynomial ωµ ∈ Pn called snake polynomial associated with µ, which oscillates most between ±µ.” "
            + "“The n-th snake polynomial ωµ is uniquely determined by the following properties: "
            + "a) |ωµ(x)| ≤ µ(x) x ∈ [−1, 1]; b) There exists a set δ* = (τi*)_{i=0}^n, "
            + "1 ≥ τ0* > · · · > τn* ≥ −1, such that ωµ(τi*) = (−1)^i µ(τi*), i = 0, . . . , n” "
            + "Conjecture verbatim: “Conjecture (G.N.) If µ ≥ 0 is a continuous even convex function in [−1, 1], "
            + "then the associated with µ snake polynomials have non-negative expansion in the Chebyshev polynomials of the first kind.”"));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Polynomial => Call("Polynomial", Real);
    private static Formula Interval => Call("Icc", Seq(Minus, D(1)), D(1));
    private static Formula Functions => Seq(Real, To, Sp, Real);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Member(Formula x, Formula set) => Seq(x, InMacro, Sp, set);
    private static Formula At(string name, Formula x) => Call(name, x);
    private static Formula BoundOnInterval(Formula body) => All("x", Real, Imp(Member(V("x"), Interval), body));

    private static Formula Snake()
    {
        Formula mu = V("mu"), n = V("n"), omega = V("omega"), tau = V("tau"), i = V("i");
        Formula indices = Call("Fin", Seq(n, Plus, D(1)));
        Formula contact = At("tau", i);
        Formula value = new Formula.Binary(new Formula.Power(Parenthesized(Seq(Minus, D(1))), i),
            FormulaBinaryOperator.Multiply, At("mu", contact));
        Formula contacts = Some("tau", Seq(indices, To, Sp, Real),
            And(Call("StrictAnti", tau), And(Leq(At("tau", D(0)), D(1)),
                And(Leq(Seq(Minus, D(1)), At("tau", Call("last", n))),
                    All("i", indices, Equal(Call("eval", omega, contact), value))))));
        Formula body = And(Leq(Call("natDegree", omega), n),
            And(BoundOnInterval(Leq(new Formula.Absolute(Call("eval", omega, V("x"))), At("mu", V("x")))), contacts));
        return Disp(All("mu", Functions, All("n", Nat, All("omega", Polynomial,
            Iff(Call("IsSnake", mu, n, omega), body)))));
    }

    private static Formula Claim()
    {
        Formula mu = V("mu"), n = V("n"), omega = V("omega"), x = V("x"), k = V("k");
        Formula term = new Formula.Binary(Call("C", At("a", k)), FormulaBinaryOperator.Multiply,
            Call("T", Real, Call("Int", k)));
        Formula expansion = Some("a", Seq(Nat, To, Sp, Real),
            And(All("k", Nat, Leq(D(0), At("a", k))),
                Equal(omega, Seq(new Formula.Subscript(Sum,
                    Seq(k, InMacro, Sp, Call("range", Seq(n, Plus, D(1))))), Sp, term))));
        Formula conclusion = All("n", Nat, All("omega", Polynomial,
            Imp(Call("IsSnake", mu, n, omega), expansion)));
        Formula body = Imp(Call("ContinuousOn", mu, Interval),
            Imp(BoundOnInterval(Leq(D(0), At("mu", x))),
                Imp(BoundOnInterval(Equal(At("mu", Seq(Minus, x)), At("mu", x))),
                    Imp(Call("ConvexOn", Real, Interval, mu), conclusion))));
        return Disp(Iff(V("claim"), All("mu", Functions, body)));
    }
}
