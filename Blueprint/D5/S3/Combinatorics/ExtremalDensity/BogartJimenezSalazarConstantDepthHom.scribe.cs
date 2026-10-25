using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class BogartJimenezSalazarConstantDepthHomDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/bogartjimenezsalazar2026twolevel");
    private const string Question = "More dramatically, do there exist strongly polynomial families G_q, H_n such that the depth function of hom(G_q, H_n) is constant while the degree function is a polynomial of positive degree?";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strongly polynomial graph families have constant depth one and growing degree.",
        H("Constant depth with a growing degree function"),
        Blocks(
            Entry("numerical", "Numerical", "Numerical polynomials", NumericalFormula(),
                "Definition 1.1, p. 2: “A numerical polynomial is a polynomial g(x) ∈ ℚ[x] such that g(q) ∈ ℤ for every q ∈ ℤ.” Integer inputs include negative integers.", true),
            Entry("two-level", "TwoLevel", "Two-level polynomials", TwoLevelFormula(),
                "Definition 1.2, p. 2: “Let g be an eventually nonnegative numerical polynomial, let S={q∈ℕ: g(q)≥0}, and let e:S → ℕ ∪ {−1,∞}.” "
                + "Definition 1.2(a): “A two-level polynomial of degree function g=g(q) and depth function e=e(q) is an infinite sequence of polynomials {f_q}_{q∈S}, with f_q(n) of degree g(q), that has the following property: writing f_q(n) = ∑_{r=0}^{∞}c_r(q)n^{g(q)−r}, where c_r(q)=0 if r>g(q), there exist polynomials {φ_r(q)}_{r≥0} such that, for every q∈S and every r ≤ e(q), we have c_r(q) = φ_r(q).” "
                + "Definition 1.2(b): “For q∈ℕ∖S, define f_q(n)=0 and e(q)=−1, extending the definition of f_q(n) to all q∈ℕ.” WithTop ℤ with the lower bound −1 represents the permitted depth values; φ is indexed by natural codegrees.", true),
            Entry("constant-depth", "constantDepth", "Constant depth on the nonnegative locus", ConstantDepthFormula(),
                "Definition 1.2(b), p. 2: “For q∈ℕ∖S, define f_q(n)=0 and e(q)=−1, extending the definition of f_q(n) to all q∈ℕ.” On S, the integer d is viewed in WithTop ℤ.", true),
            Entry("strongly-polynomial", "StronglyPolynomial", "Strongly polynomial graph sequences", StronglyFormula(),
                "Definition 3.2, p. 9: “A sequence {G_n}_{n≥0} of graphs is strongly polynomial if, for every fixed graph F, there exists a polynomial p_F(n) such that hom(F,G_n)=p_F(n).” The finite simple graphs have Fin-labelled vertices. The count is the cardinality of all adjacency-preserving maps; injectivity is not required. The quantifiers include a=0 and q=0. Rational polynomials represent integer-valued polynomial count functions.", true),
            Entry("claim", "claim", "Question 3.19", EqTo(V("claim"), ClaimBody()),
                "Question 3.19, p. 14, verbatim: “" + Question + "” The assertion quantifies over arbitrary finite simple graph sequences. Depth means maximal uniform integer constant depth: some d≥−1 works for all nonnegative parameters, and every larger integer constant fails. This does not assert a pointwise greatest depth function.", true),
            Entry("result", "result", "An affirmative answer to Question 3.19", ClaimBody(),
                "Take G_q=K_{q+3,2} and H_n=K_{1,n,n}. Their homomorphism count is 2n²(n+1)^(q+3)+4n^(q+4)+2^(q+3)n^(q+3)+2n². Its degree is q+5. The first three codegree coefficients are 2, 2q+10, and (q+3)(q+2)+2^(q+3). The first two are polynomial in q; the third cannot be polynomial, since sufficiently many forward differences annihilate a polynomial and preserve the exponential 2^(q+3). Fixed finite proper colourings and independent choices inside each target part give strong polynomiality of both sequences. The formula and the colouring argument include parameter zero and the empty fixed graph.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19"), ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rational => Seq(Mathbb, Grp(V("Q")));
    private static Formula Poly => Call("Polynomial", Rational);
    private static Formula TopZ => Call("WithTop", Integer);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Field(Formula owner, string name) => Seq(Parenthesized(owner), Dot, Operatorname, Grp(V(name)));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula DependentGraph(string parameter, Formula size) =>
        Arrow(Parenthesized(Seq(V(parameter), Colon, Sp, Natural)), Call("SimpleGraph", Call("Fin", size)));
    private static Formula Cast(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula Eval(Formula p, string variable, Formula domain) => App(Field(p, "eval"), Cast(V(variable), domain));
    private static Formula Degree(Formula p) => Field(p, "natDegree");
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula EqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Conj(params Formula[] parts) => parts.Length == 1 ? parts[0] :
        new Formula.Logic(Parenthesized(parts[0]), FormulaLogicOperator.And, Parenthesized(Conj(parts[1..])));
    private static Formula Not(Formula body) => Seq(Neg, Sp, Parenthesized(body));
    private static Formula MinusOne => new Formula.Negate(N(1));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        App(V("ite"), Parenthesized(condition), Parenthesized(yes), Parenthesized(no));
    private static Formula Nonnegative(string variable) => Le(N(0), Eval(V("g"), variable, Rational));
    private static Formula NumericalFormula() => All("g", Poly,
        EqTo(Call("Numerical", V("g")), All("z", Integer, ExistsOne("k", Integer,
            EqTo(Eval(V("g"), "z", Rational), Cast(V("k"), Rational))))));
    private static Formula TwoLevelFormula() => All("f", Arrow(Natural, Poly), All("g", Poly, All("e", Arrow(Natural, TopZ),
        EqTo(Call("TwoLevel", V("f"), V("g"), V("e")), Conj(
            Call("Numerical", V("g")), ExistsOne("b", Natural, All("q", Natural, Imp(Le(V("b"), V("q")), Nonnegative("q")))),
            All("q", Natural, Imp(Nonnegative("q"), Le(Cast(Cast(MinusOne, Integer), TopZ), App(V("e"), V("q"))))),
            All("q", Natural, Imp(Nonnegative("q"), Conj(Ne(App(V("f"), V("q")), N(0)),
                EqTo(Cast(Degree(App(V("f"), V("q"))), Rational), Eval(V("g"), "q", Rational))))),
            All("q", Natural, Imp(Lt(Eval(V("g"), "q", Rational), N(0)),
                Conj(EqTo(App(V("f"), V("q")), N(0)), EqTo(App(V("e"), V("q")), Cast(Cast(MinusOne, Integer), TopZ))))),
            ExistsOne("phi", Arrow(Natural, Poly), All("q", Natural, All("r", Natural,
                Imp(Nonnegative("q"), Imp(Le(Cast(V("r"), TopZ), App(V("e"), V("q"))),
                    EqTo(If(Le(V("r"), Degree(App(V("f"), V("q")))), App(Field(App(V("f"), V("q")), "coeff"), new Formula.Binary(Degree(App(V("f"), V("q"))), FormulaBinaryOperator.Subtract, V("r"))), N(0)), Eval(App(V("phi"), V("r")), "q", Rational))))))))))));
    private static Formula ConstantDepthFormula() => All("g", Poly, All("d", Integer, All("q", Natural,
        EqTo(Call("constantDepth", V("g"), V("d"), V("q")),
            If(Nonnegative("q"), Cast(V("d"), TopZ), Cast(Cast(MinusOne, Integer), TopZ))))));
    private static Formula StronglyFormula() => All("v", Arrow(Natural, Natural),
        All("G", DependentGraph("q", App(V("v"), V("q"))), EqTo(Call("StronglyPolynomial", V("v"), V("G")),
            All("a", Natural, All("F", Call("SimpleGraph", Call("Fin", V("a"))), ExistsOne("p", Poly,
                All("q", Natural, EqTo(Cast(App(Qualified("ThreeClassHomomorphismLimit", "homCount"), V("F"), App(V("G"), V("q"))), Rational), Eval(V("p"), "q", Rational)))))))));
    private static Formula ClaimBody() => ExistsOne("v", Arrow(Natural, Natural), ExistsOne("w", Arrow(Natural, Natural),
        ExistsOne("G", DependentGraph("q", App(V("v"), V("q"))), ExistsOne("H", DependentGraph("n", App(V("w"), V("n"))),
        ExistsOne("f", Arrow(Natural, Poly), ExistsOne("g", Poly, ExistsOne("d", Integer, Conj(
            Le(MinusOne, V("d")), Call("StronglyPolynomial", V("v"), V("G")), Call("StronglyPolynomial", V("w"), V("H")),
            All("q", Natural, All("n", Natural, EqTo(Cast(App(Qualified("ThreeClassHomomorphismLimit", "homCount"), App(V("G"), V("q")), App(V("H"), V("n"))), Rational), Eval(App(V("f"), V("q")), "n", Rational)))),
            Lt(N(0), Degree(V("g"))), Call("TwoLevel", V("f"), V("g"), Call("constantDepth", V("g"), V("d"))),
            All("b", Integer, Imp(Lt(V("d"), V("b")), Not(Call("TwoLevel", V("f"), V("g"), Call("constantDepth", V("g"), V("b"))))))))))))));
}
