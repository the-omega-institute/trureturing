using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Lemniscates;

internal sealed class FeketeLemniscateAreaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/ghosh2026erdos");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree-four Fekete polynomial on the connected interval [−20,20] has larger unit-lemniscate area than a monic competitor with zeros in the same interval.",
        H("Fekete Lemniscate Area Refutation"),
        Blocks(
            Entry("vandermonde", "vandermonde", "The Vandermonde product", Vandermonde(),
                "The product of pairwise distances is taken once for each ordered index pair i<j. "
                + "The tuple is indexed by Fin n, so repeated entries are permitted and give a zero product.",
                DescribeRole.Definition, true),
            Entry("fekete-tuple", "IsFeketeTuple", "Fekete tuples", FeketeTuple(),
                "A tuple in K is Fekete when its Vandermonde product is at least that of every other n-tuple in K. "
                + "This definition does not assume compactness or connectedness; those hypotheses occur in the minimization claim.",
                DescribeRole.Definition, true),
            Entry("polynomial-class", "InP", "The admissible polynomial class", PolynomialClass(),
                "Section 1 defines P_n(K) as the monic degree-n polynomials with all zeros in K. "
                + "The Lean predicate uses natDegree and requires membership in K for every complex root.",
                DescribeRole.Definition, true),
            Entry("area", "lemniscateArea", "Unit-lemniscate area", Area(),
                "Section 1 defines Λ_p={z:|p(z)|<1}. Its area is planar Lebesgue measure, "
                + "represented by volume on ℂ and valued in the extended non-negative reals. "
                + "The source's A_n(K) is the infimum of these areas over P_n(K).",
                DescribeRole.Definition, true),
            Entry("minimization-claim", "claim", "The connected-set minimization claim", Claim(),
                "Immediately after Proposition 3.6: “While the above proposition proves that Fekete polynomials "
                + "are not area minimizers in general, it would be of interest to know if they are minimzers "
                + "when the set K is connected. We leave this as an open question.” "
                + "The claim expresses exact minimization for every compact connected K, every positive degree, "
                + "every Fekete tuple and every admissible competitor, using a pairwise area comparison.",
                DescribeRole.Definition, true),
            Entry("inner-disc", "ball_subset_lemniscate", "An inner-disc certificate", InnerDisc(),
                "For any finite complex root family, the triangle inequality bounds each other factor on a disc "
                + "about the selected root. If the displayed product bound is less than one, the entire open disc "
                + "lies inside the unit lemniscate. No root separation hypothesis is needed.",
                DescribeRole.Theorem, false),
            Entry("outer-cover", "lemniscate_subset_balls", "A three-regime disc cover", OuterCover(),
                "The root family is nonempty. Separation by 2t permits three cases for the distance to a nearest root: "
                + "less than e, between e and t, and at least t. The near, middle and far product bounds "
                + "exclude any point outside the proposed discs from the unit lemniscate. "
                + "The radii r_i are arbitrary real numbers subject to the displayed bounds; the theorem does not add a positivity assumption on them.",
                DescribeRole.Theorem, false),
            Entry("interval-four", "isFeketeTuple_interval_four", "Four Fekete points on an interval", IntervalFour(),
                "For R>0 and u>0 with 5u²=R², the tuple (−R,−u,u,R) is Fekete on the real interval embedded in ℂ. "
                + "The proof bounds every Vandermonde product by 4Ru(R²−u²)², attained by this tuple. "
                + "With u=R/√5 the value is 64R⁶/(25√5). This exhibits a maximizing tuple without asserting uniqueness.",
                DescribeRole.Theorem, false),
            Entry("refutation", "result", "Connectedness does not ensure exact minimization", Disp(Seq(Neg, Sp, F.Id("claim"))),
                "Take K=[−20,20] embedded in ℂ and n=4. The Fekete polynomial is F(z)=(z²−400)(z²−80); "
                + "the competitor is G(z)=(z²−400)(z²−100). Disjoint discs inside Λ_F have radii "
                + "97/1250000 at ±20 and 217/1250000 at ±√80. A cover of Λ_G has radii "
                + "53/625000 at ±20 and 849/5000000 at ±10, certified with e=1/10 and t=5. "
                + "Hence area(Λ_F) ≥ π·7231744/10¹⁴ > π·7204616/10¹⁴ ≥ area(Λ_G). "
                + "The interval is compact and connected, and G is monic of degree four with all roots in K. "
                + "The contradiction concerns exact optimality; the paper's logarithmic asymptotic optimality in Theorem 3.1 is unaffected.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Commentary(name, prose), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ghosh-ramachandran-2026-fekete-lemniscate-area"),
                ResolutionKind.Refuted) : null);

    private static BlockSequence Commentary(string name, string prose)
    {
        if (name != "claim") return Blocks(Paragraph(Text(prose)));
        return Blocks(
            Paragraph(Text("Immediately after Proposition 3.6, verbatim: “While the above proposition proves "
                + "that Fekete polynomials are not area minimizers in general, it would be of interest to know "
                + "if they are minimzers when the set "), Math(F.Id("K")),
                Text(" is connected. We leave this as an open question.”")),
            Paragraph(Text("For compact connected K and n≥1, every Fekete tuple defines a monic polynomial "
                + "with all roots in K. The pairwise comparison against every polynomial in P_n(K) expresses "
                + "exact minimization of the unit-lemniscate area, whose infimum is A_n(K).")));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula x, Formula i) => new Formula.Apply(x, [i]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Roots(Formula n) => Seq(Fin(n), To, Sp, Complex);
    private static Formula Polynomial => Call("Polynomial", Complex);
    private static Formula Sets => Call("Set", Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, P(y));
    private static Formula Member(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Subset(Formula x, Formula y) => Seq(x, Sp, Subseteq, Sp, y);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Dist(Formula c, Formula i, Formula j) => Norm(Sub(At(c, i), At(c, j)));
    private static Formula Prod(Formula index, Formula set, Formula body) =>
        Seq(F.Prod, Underscore, Grp(Member(index, set)), Sp, P(body));
    private static Formula Others(Formula n, Formula k) => Call("erase", Call("univ", Fin(n)), k);
    private static Formula RootPolynomial(Formula n, Formula c) =>
        Prod(V("i"), Fin(n), Sub(V("X"), Call("C", At(c, V("i")))));
    private static Formula Level(Formula n, Formula c) => LevelOf(RootPolynomial(n, c));
    private static Formula LevelOf(Formula p) => Seq(Left, OpenBrace, V("z"), Colon, Sp, Complex,
        Sp, Mid, Sp, Less(Norm(Call("eval", p, V("z"))), D(1)), Right, CloseBrace);
    private static Formula Ball(Formula c, Formula r) => Call("ball", c, r);

    private static Formula Vandermonde()
    {
        Formula n = V("n"), a = V("a"), i = V("i"), j = V("j");
        return Disp(All("n", Nat, All("a", Roots(n), Eqn(Call("vandermonde", a),
            Prod(i, Fin(n), Prod(j, Call("Ioi", i), Dist(a, i, j)))))));
    }

    private static Formula FeketeTuple()
    {
        Formula n = V("n"), a = V("a"), b = V("b"), k = V("K");
        Formula InK(Formula c) => All("i", Fin(n), Member(At(c, V("i")), k));
        Formula maximum = All("b", Roots(n),
            Imp(InK(b), Leq(Call("vandermonde", b), Call("vandermonde", a))));
        return Disp(All("K", Sets, All("n", Nat, All("a", Roots(n),
            Iff(Call("IsFeketeTuple", k, a), And(InK(a), maximum))))));
    }

    private static Formula PolynomialClass()
    {
        Formula k = V("K"), n = V("n"), p = V("p");
        Formula rootCondition = All("z", Complex,
            Imp(Call("IsRoot", p, V("z")), Member(V("z"), k)));
        Formula body = And(Call("Monic", p), And(Eqn(Call("natDegree", p), n), rootCondition));
        return Disp(All("K", Sets, All("n", Nat, All("p", Polynomial,
            Iff(Call("InP", k, n, p), body)))));
    }

    private static Formula Area() => Disp(All("p", Polynomial,
        Eqn(Call("lemniscateArea", V("p")), Call("volume", LevelOf(V("p"))))));

    private static Formula Claim()
    {
        Formula k = V("K"), n = V("n"), a = V("a"), p = V("p");
        Formula comparison = All("p", Polynomial, Imp(Call("InP", k, n, p),
            Leq(Call("lemniscateArea", RootPolynomial(n, a)), Call("lemniscateArea", p))));
        Formula hypotheses = Imp(Call("IsConnected", k), Imp(Call("IsCompact", k),
            Imp(Call("IsFeketeTuple", k, a), comparison)));
        return Disp(Iff(V("claim"), All("K", Sets, All("n", Nat,
            Imp(Leq(D(1), n), All("a", Roots(n), hypotheses))))));
    }

    private static Formula InnerDisc()
    {
        Formula n = V("n"), c = V("c"), k = V("k"), r = V("r");
        Formula bound = Less(Mul(r, Prod(V("j"), Others(n, k), Add(Dist(c, k, V("j")), r))), D(1));
        return Disp(All("n", Nat, All("c", Roots(n), All("k", Fin(n), All("r", Real,
            Imp(Less(D(0), r), Imp(bound, Subset(Ball(At(c, k), r), Level(n, c)))))))));
    }

    private static Formula OuterCover()
    {
        Formula n = V("n"), c = V("c"), r = V("r"), e = V("e"), t = V("t");
        Formula Distinct(Formula body) => All("i", Fin(n), All("j", Fin(n),
            Imp(Seq(V("i"), Neq, Sp, V("j")), body)));
        Formula sep = Distinct(Leq(Mul(D(2), t), Dist(c, V("i"), V("j"))));
        Formula near = All("k", Fin(n), Leq(D(1), Mul(At(r, V("k")),
            Prod(V("j"), Others(n, V("k")), Sub(Dist(c, V("k"), V("j")), e)))));
        Formula positive = Distinct(Leq(e, Dist(c, V("i"), V("j"))));
        Formula cover = Call("iUnion", Seq(V("i"), Colon, Sp, Fin(n), Sp, Mapsto, Sp,
            Ball(At(c, V("i")), At(r, V("i")))));
        Formula body = Imp(Less(D(0), e), Imp(Less(D(0), t), Imp(sep, Imp(near,
            Imp(positive, Imp(Leq(D(1), Mul(e, Pow(t, Sub(n, D(1))))),
                Imp(Leq(D(1), Pow(t, n)), Subset(Level(n, c), cover))))))));
        return Disp(All("n", Nat, Imp(Less(D(0), n), All("c", Roots(n),
            All("r", Seq(Fin(n), To, Sp, Real), All("e", Real, All("t", Real, body)))))));
    }

    private static Formula IntervalFour()
    {
        Formula r = V("R"), u = V("u");
        Formula ofReal = Seq(Operatorname, Grp(V("Complex")), Dot, Operatorname, Grp(V("ofReal")));
        Formula interval = Call("image", ofReal, Call("Icc", Seq(Minus, r), r));
        Formula tuple = Seq(Open, Seq(Minus, r), Comma, Seq(Minus, u), Comma, u, Comma, r, Close);
        Formula roots = P(Seq(V("i"), Colon, Sp, Fin(D(4)), Sp, Mapsto, Sp,
            P(Seq(At(tuple, V("i")), Colon, Sp, Complex))));
        return Disp(All("R", Real, All("u", Real, Imp(Less(D(0), r), Imp(Less(D(0), u),
            Imp(Eqn(Mul(D(5), Pow(u, D(2))), Pow(r, D(2))), Call("IsFeketeTuple", interval, roots)))))));
    }
}
