using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hyperbolic;

internal sealed class HiraiNieuwboerWalterCothConstantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/hirai2023interiorpoint");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal real coefficient in the Hirai–Nieuwboer–Walter hyperbolic cotangent inequality is one over the square root of two.",
        H("The optimal hyperbolic cotangent constant"), Blocks(
            Paragraph(Text("Hirai–Nieuwboer–Walter, arXiv:2303.04771v2, §5, Lemma 5.13 and Remark 5.14:")),
            Paragraph(Text("“Lemma 5.13. The constant C = √2 is such that for all a, b ∈ ℝ, one has |coth((a − b)/2) (a coth(a/2) − b coth(b/2))| ≤ C √(ab(a − b) coth(a/2) coth(b/2) coth((a − b)/2)).”")),
            Paragraph(Text("“Remark 5.14. We conjecture, based on numerical evidence, that the optimal constant in the above inequality is C = 1/√2.”")),
            Paragraph(Text("The source proves the coefficient √2 and conjectures the optimal coefficient 1/√2. "
                + "The repository resolves that conjecture: the optimal constant in "), Math(SourceInequality()),
                Text(" is C = 1/√2. The inputs are distinct nonzero real numbers. "
                    + "The assertion comprises the uniform inequality and a strict counterexample for every smaller real coefficient.")),
            Node("cothR", "Real hyperbolic cotangent", All("x", Equal(Call("cothR", N("x")),
                Frac(Call("cosh", N("x")), Call("sinh", N("x"))))),
                DescribeRole.Definition, "The quotient specifies the real hyperbolic cotangent."),
            Node("lhs", "Absolute cotangent difference", All("a", All("b", Equal(Lhs(),
                Call("abs", Multiply(Call("cothR", Half(Subtract(N("a"), N("b")))),
                    Subtract(Multiply(N("a"), Call("cothR", Half(N("a")))),
                        Multiply(N("b"), Call("cothR", Half(N("b")))))))))),
                DescribeRole.Definition, "The absolute value is taken after multiplying by the cotangent of the half-difference."),
            Node("radicand", "Positive hyperbolic product", All("a", All("b", Equal(Radicand(),
                Product(N("a"), N("b"), Subtract(N("a"), N("b")),
                    Call("cothR", Half(N("a"))), Call("cothR", Half(N("b"))),
                    Call("cothR", Half(Subtract(N("a"), N("b")))))))),
                DescribeRole.Definition, "On the permitted domain each factor x coth(x/2) is strictly positive."),
            Node("claim", "The uniform estimate and optimality", Equal(N("claim"), ClaimBody()),
                DescribeRole.Definition, "The first conjunct includes both signs of both inputs. "
                    + "The second quantifies over every real coefficient strictly below 1/√2."),
            Node("result", "Optimal coefficient one over square root two", ClaimBody(),
                DescribeRole.Theorem, "The estimate holds at 1/√2, and every smaller real coefficient admits "
                    + "distinct nonzero real inputs with a strict reverse inequality.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hirai-nieuwboer-walter-2023-coth-constant"), ResolutionKind.Proved)),
            Paragraph(Text("Extend u(x)=x coth(x) by u(0)=1 and put ψ(x)=x tanh(x). "
                + "The function u is even, at least one, nondecreasing and 1-Lipschitz on the nonnegative half-line. "
                + "The function ψ is even and nondecreasing there, and u(x)ψ(x)=x². "
                + "For A=max(|x|,|y|), B=min(|x|,|y|), δ=A−B and D=|x−y|, "
                + "the Lipschitz bound gives (u(x)−u(y))²≤δ²=ψ(δ)u(δ)≤ψ(D)u(A)u(B). "
                + "The substitutions a=2x and b=2y turn this into the squared ratio bound 1/2.")),
            Paragraph(Text("For C<1/√2, choose t=2/(1−C√2)>0. Since u(t)≥t, "
                + "u(t)−1−Ct√2≥1>0. The continuous function "
                + "F(y)=u(t−y)(u(t)−u(y))−C(t−y)√(2u(t)u(y)u(t−y)) "
                + "is strictly positive at y=0. It remains positive for some small y with 0<y<t. "
                + "The pair a=2t, b=2y is then a strict violation at coefficient C, proving sharpness. "
                + "Through the paper's Theorem 5.15, the scalar estimate gives the consequence "
                + "“squared distance on PD(n) is 8-self-concordant”; this geometric consequence is not formalized here.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        string prose, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hirai-coth-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            name == "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula N(string x) => F.Id(x);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula All(string x, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), R(), body);
    private static Formula Some(string x, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), R(), body);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Half(Formula x) => Frac(x, D(2));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Product(params Formula[] xs)
    {
        Formula product = xs[0];
        for (int i = 1; i < xs.Length; i++) product = Multiply(product, xs[i]);
        return product;
    }
    private static Formula Lhs() => Call("lhs", N("a"), N("b"));
    private static Formula Radicand() => Call("radicand", N("a"), N("b"));
    private static Formula Root() => Call("sqrt", Radicand());
    private static Formula Constant() => Frac(D(1), Call("sqrt", D(2)));
    private static Formula SourceInequality() => Le(
        Call("abs", Multiply(Call("cothR", Half(Subtract(N("a"), N("b")))),
            Subtract(Multiply(N("a"), Call("cothR", Half(N("a")))),
                Multiply(N("b"), Call("cothR", Half(N("b"))))))),
        Multiply(N("C"), Call("sqrt", Product(N("a"), N("b"), Subtract(N("a"), N("b")),
            Call("cothR", Half(N("a"))), Call("cothR", Half(N("b"))),
            Call("cothR", Half(Subtract(N("a"), N("b"))))))));
    private static Formula ClaimBody() => And(
        All("a", All("b", Imp(Ne(N("a"), D(0)), Imp(Ne(N("b"), D(0)),
            Imp(Ne(N("a"), N("b")), Le(Lhs(), Multiply(Constant(), Root()))))))),
        All("C", Imp(Lt(N("C"), Constant()), Some("a", Some("b",
            And(Ne(N("a"), D(0)), And(Ne(N("b"), D(0)),
                And(Ne(N("a"), N("b")), Lt(Multiply(N("C"), Root()), Lhs())))))))));
}
