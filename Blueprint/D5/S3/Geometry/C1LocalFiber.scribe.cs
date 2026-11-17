using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class C1LocalFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/C1LocalFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual local fibers of finite-dimensional real C1 maps", H("C1 local fibers and dimension obstruction"),
        Blocks(
            Item("linear-vertical-eq-zero", "linear_vertical_eq_zero", "The vertical rank criterion",
                "For a linear map T from R times K to G over a division ring, suppose an observed linear projection p satisfies p composed with T equals the first coordinate. If the range dimension of T is at most the dimension of R, every vector (0,z) is killed by T. Restrict p to the actual range of T: it is surjective, the dimension bound makes it injective, and its kernel therefore vanishes. The argument adapts BochaoKong's Apache-2.0 LeanPool complex constant-rank linear algebra, commit 2b1ec889365345f19a45fa94b6457a4d92c96295. It is consumed by the real fiber construction and by finite matrix completion."),
            Item("exists-local-fiber", "exists_local_fiber", "An actual C1 ball in a level set",
                "Let f be real C1 on an open set U and a belong to U. Assume the derivative rank at a bounds the derivative rank at every point of U. The theorem constructs a subspace K, a continuous linear map q, a map k and a positive radius. The dimension of K plus the derivative rank at a equals the source dimension. On the K-ball, k is C1, k(0)=a, k(z) belongs to U, f(k(z))=f(a), and q(k(z)-a)=z. Thus distinct ball parameters give distinct actual source points, including when the maximal rank is zero. Complementary range and kernel projections make the derivative of the centered coordinate map invertible. A local inverse supplies the coordinates. The rank criterion kills all vertical derivatives; the convex-ball zero-derivative theorem supplies equality of values. Neither a derivative kernel alone nor a formal tangent direction is presented as a fiber."),
            Item("exists-collision", "exists_collision", "Collision in every nonempty open domain",
                "A real C1 map from a finite-dimensional normed space to a strictly smaller one has two distinct source points in any specified nonempty open domain with identical output. The bounded integer-valued derivative rank attains a maximum on that domain. The constructed local fiber then has positive dimension, and a nonzero vector in its ball produces the collision. No compactness of the domain and no density of the global maximum-rank set are assumed."),
            Item("not-injon", "not_injOn", "Open-domain noninjectivity",
                "The actual collision immediately excludes injectivity on the nonempty open domain. This is an analysis supplier for the twelve-real-coordinate MPS record. By itself it neither proves two-site density minimality nor supplies a nonempty phase-identifiable MPS chart."))));

    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula X(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(X("R")));
    private static Formula Type => Seq(X("Type"), Star);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(x), Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] fs) => fs.Aggregate((a, b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Member(Formula x, Formula s) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Pair(Formula x, Formula y) => Par(Seq(x, Comma, Sp, y));
    private static Formula Rank(Formula field, Formula space) => At("finrank", field, space);
    private static Formula Product(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Linear(Formula field, Formula a, Formula b) => At("LinearMap", field, a, b);
    private static Formula CLM(Formula a, Formula b) => At("ContinuousLinearMap", Real, a, b);
    private static Formula Space(string name, Formula field, Formula body, bool normed)
    {
        var x = X(name);
        return All(name, Type, normed
            ? Seq(Inst(At("NormedAddCommGroup", x)), Inst(At("NormedSpace", field, x)),
                Inst(At("FiniteDimensional", field, x)), body)
            : Seq(Inst(At("AddCommGroup", x)), Inst(At("Module", field, x)),
                Inst(At("FiniteDimensional", field, x)), body));
    }
    private static Formula DerivativeRank(Formula x) =>
        Rank(Real, At("range", At("fderiv", Real, X("f"), x)));
    private static Formula Source(Formula body) =>
        Space("E", Real, Space("F", Real,
            All("U", At("Set", X("E")), All("f", Arrow(X("E"), X("F")),
                Imp(At("IsOpen", X("U")), Imp(At("ContDiffOn", Real, D(1), X("f"), X("U")), body)))), true), true);

    private static Formula Collision() => Some("x", X("E"), And(Member(X("x"), X("U")),
        Some("y", X("E"), And(Member(X("y"), X("U")),
            new Formula.Not(Eqn(X("x"), X("y"))), Eqn(At("f", X("x")), At("f", X("y")))))));

    private static Formula Statement(string name)
    {
        if (name == "linear_vertical_eq_zero")
        {
            var field = X("kappa");
            var result = All("T", Linear(field, Product(X("R"), X("K")), X("G")),
                All("p", Linear(field, X("G"), X("R")),
                    Imp(Eqn(At("comp", X("p"), X("T")), At("fst", field, X("R"), X("K"))),
                        Imp(Le(Rank(field, At("range", X("T"))), Rank(field, X("R"))),
                            All("z", X("K"), Eqn(At("T", Pair(D(0), X("z"))), D(0)))))));
            return All("kappa", Type, Seq(Inst(At("DivisionRing", field)),
                Space("R", field, Space("K", field, Space("G", field, result, false), false), false)));
        }
        if (name == "exists_local_fiber")
        {
            var ball = At("ball", D(0), X("epsilon"));
            var kz = At("k", X("z"));
            var law = All("z", X("K"), Imp(Member(X("z"), ball),
                And(Member(kz, X("U")), Eqn(At("f", kz), At("f", X("a"))),
                    Eqn(At("q", new Formula.Binary(kz, FormulaBinaryOperator.Subtract, X("a"))), X("z")))));
            var properties = And(Lt(D(0), X("epsilon")),
                Eqn(new Formula.Binary(Rank(Real, X("K")), FormulaBinaryOperator.Add,
                    DerivativeRank(X("a"))), Rank(Real, X("E"))),
                Eqn(At("k", D(0)), X("a")), At("ContDiffOn", Real, D(1), X("k"), ball), law);
            var fiber = Some("K", At("Submodule", Real, X("E")),
                Some("q", CLM(X("E"), X("K")),
                    Some("k", Arrow(X("K"), X("E")), Some("epsilon", Real, properties))));
            return Source(All("a", X("E"), Imp(Member(X("a"), X("U")),
                Imp(All("x", X("E"), Imp(Member(X("x"), X("U")),
                    Le(DerivativeRank(X("x")), DerivativeRank(X("a"))))), fiber))));
        }
        var conclusion = name == "not_injOn"
            ? new Formula.Not(At("InjOn", X("f"), X("U")))
            : Collision();
        return Source(Imp(At("Nonempty", X("U")),
            Imp(Lt(Rank(Real, X("F")), Rank(Real, X("E"))), conclusion)));
    }
}
