using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class JNRRemarkThirteenPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/JNRRemarkThirteenPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/corkdisneyhogg2025jnr");
    private const string Conjecture =
        "Appendix A, Remark 13, PDF page 20 (printed page 19): “The above proof shows that this is positive so long as Σᵢ (λᵢ²/|yᵢ|²) yᵢ = 0, however we conjecture that the sum in (18) is positive for any choice of yᵢ ∈ ℝ³∖{aᵢ}.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The JNR triple sum is positive for every configuration of distinct poles with positive weights.",
        H("A sum of squares for the JNR triple sum"),
        Blocks(
            Paragraph(Text("Cork and Disney-Hogg's expression (18) has two outer sums that can be combined into inner products of weighted vector sums. Completing a square at a weighted barycentre proves positivity without the balance condition (15). All sums below range over Fin (N + 1), so each ordered triple, including repeated indices, is counted once.")),
            Node("rho0", "The zero-parameter density", "rho0", DescribeRole.Definition,
                Parameters(false, Eq(Call("rho0", X("lam"), X("y")), RhoBody())),
                AssessedProvenance.FromLiterature(Source),
                "Equation (3), PDF page 4 (printed page 3), defines “ρ(μ) = Σ_{i=0}^N λᵢ² / |x − aᵢ + μ|²”. At μ = 0, with yᵢ = aᵢ − x and the Euclidean norm of pure imaginary quaternions, this is the displayed density. The weights are the real function lam and the vectors form the function y; the definition uses total real division."),
            Node("sum", "The triple sum in expression (18)", "S", DescribeRole.Definition,
                Parameters(true, Eq(Call("S", X("lam"), X("mu"), X("y")), SumBody())),
                AssessedProvenance.FromLiterature(Source),
                "Appendix A, Remark 13, PDF page 20 (printed page 19): “As a consequence of (15), we can write” expression (18), followed by “where ρ(μ) is given in (3), and yᵢ = aᵢ − x_∗.” The displayed definition is that expression, with real inner product inner ℝ, lam for λ and mu for μ. Its value is defined for all inputs by total real division; positivity requires the hypotheses below."),
            Node("claim", "The positivity conjecture", "claim", DescribeRole.Definition,
                Eq(X("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Conjecture + " The index type Fin (N + 1) represents the N + 1 poles and 1 ≤ N ensures at least two of them. The poles a are injective, lam is positive at each pole, mu is positive, and x differs from every a i. The source's exclusion is read as x ≠ a i, hence a i − x ≠ 0. No balance equation is assumed."),
            Node("result", "Strict positivity for every configuration", "result", DescribeRole.Theorem,
                ClaimBody(), AssessedProvenance.FromRepo(Source),
                "Set yᵢ = aᵢ − x, wᵢ = lam(i)², rᵢ = ‖yᵢ‖² and t = mu². Put αᵢ = wᵢ/(rᵢ+t), βᵢ = wᵢ/rᵢ and qᵢ = wᵢ/(rᵢ(rᵢ+t)); then βᵢ = αᵢ + t qᵢ. Let A = Σᵢ αᵢ, B = Σᵢ αᵢ yᵢ, C = Σᵢ βᵢ, D = Σᵢ βᵢ yᵢ and m = C⁻¹ D. Factoring the outer sums gives C S = Σⱼ qⱼ ⟨A yⱼ − B, C yⱼ − D⟩. The relation t Σᵢ qᵢ(yᵢ − m) = A m − B gives S = A Σᵢ qᵢ ‖yᵢ − m‖² + ‖A m − B‖²/t. Every coefficient is positive. Two distinct poles force a nonzero displacement from m, so the first term is positive and the second is nonnegative."),
            Paragraph(Text("The private algebraic identities hold for every finite family in any real inner-product space. Strictness only needs two different vectors. For a constant family every original inner-product difference is zero; together these facts characterize the equality case. If D = 0, then m = 0 and the second square is ‖B‖²/t, which need not vanish. The conclusion concerns expression (18): equality with the source's earlier double sum away from (15), and physical realizations, are separate questions.")))));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("jnr-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sq(Formula body) => new Formula.Power(body, D(2));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Indices() => Call("Fin", Parenthesized(Add(X("N"), D(1))));
    private static Formula Space() => Call("EuclideanSpace", Real(), Parenthesized(Call("Fin", D(3))));
    private static Formula At(string function, string index) => Call(function, X(index));
    private static Formula NormSq(string index) => Sq(new Formula.Norm(At("y", index)));
    private static Formula SumAt(string index, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(X(index), Sp, Colon, Sp, Indices())), Sp, body);
    private static Formula Parameters(bool withMu, Formula body) => All("N", Nat(),
        All("lam", Arrow(Indices(), Real()),
            withMu ? All("mu", Real(), All("y", Arrow(Indices(), Space()), body))
                : All("y", Arrow(Indices(), Space()), body)));
    private static Formula RhoBody() => SumAt("i", Div(Sq(At("lam", "i")), NormSq("i")));
    private static Formula SumBody()
    {
        var differenceLeft = Parenthesized(Sub(At("y", "j"), At("y", "i")));
        var differenceRight = Parenthesized(Sub(At("y", "j"), At("y", "k")));
        var weights = Mul(Mul(Sq(At("lam", "i")), Sq(At("lam", "j"))), Sq(At("lam", "k")));
        var numerator = Mul(weights, Call("inner", Real(), differenceLeft, differenceRight));
        var denominator = Mul(Mul(Mul(Parenthesized(Add(NormSq("i"), Sq(X("mu")))),
            Parenthesized(Add(NormSq("j"), Sq(X("mu"))))), NormSq("j")), NormSq("k"));
        var triple = SumAt("i", SumAt("j", SumAt("k", Div(numerator, denominator))));
        return Mul(Div(D(1), Call("rho0", X("lam"), X("y"))), Parenthesized(triple));
    }
    private static Formula ClaimBody()
    {
        var shifted = Parenthesized(Seq(LambdaLower, Sp, X("i"), Sp, Mapsto, Sp,
            Sub(At("a", "i"), X("x"))));
        Formula body = Lt(D(0), Call("S", X("lam"), X("mu"), shifted));
        body = Imp(All("i", Indices(), new Formula.Relation(X("x"),
            FormulaRelationOperator.NotEqual, At("a", "i"))), body);
        body = Imp(App(Qualified("Function", "Injective"), X("a")), body);
        body = Imp(Lt(D(0), X("mu")), body);
        body = Imp(All("i", Indices(), Lt(D(0), At("lam", "i"))), body);
        body = All("lam", Arrow(Indices(), Real()), All("mu", Real(),
            All("a", Arrow(Indices(), Space()), All("x", Space(), body))));
        return All("N", Nat(), Imp(new Formula.Relation(D(1),
            FormulaRelationOperator.LessThanOrEqual, X("N")), body));
    }
}
