using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class GeorgeTomamichelMaximalCorrelationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/georgetomamichel2025correlation");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric maximal correlation one forces arithmetic maximal correlation one.",
        H("The arithmetic and geometric endpoints"), Blocks(
            Node("correlation-values", "correlationValues", "Feasible Hermitian correlation values", ValuesDefinition(),
                "Definition 24, equation (54), page 19: “where the maximization is over X ∈ Herm(A), Y ∈ Herm(B).” The displayed set consists of the feasible absolute traces with zero marginal expectation and unit quadratic norm. The index types are arbitrary finite types; the marginal matrices are the two finite partial sums.", true, DescribeRole.Definition),
            Node("arithmetic-coefficient", "muAM", "Arithmetic maximal correlation", CoefficientDefinition("muAM", ArithmeticMap()),
                "The arithmetic mean gives the linear mean operator X ↦ (sigma X + X sigma)/2. The coefficient is the supremum of the feasible absolute correlations.", true, DescribeRole.Definition),
            Node("geometric-coefficient", "muGM", "Geometric maximal correlation", CoefficientDefinition("muGM", GeometricMap()),
                "The geometric mean gives X ↦ sqrt(sigma) X sqrt(sigma). The real supremum of an empty feasible set is zero.", true, DescribeRole.Definition),
            Node("endpoint-claim", "claim", "The endpoint proposition", Eqn(Q("claim"), ClaimBody()),
                "Section VII, page 66: “Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?” Here rho is a positive semidefinite trace-one complex matrix on a product of finite index types. The displayed implication answers the question negatively, including states with singular marginals.", true, DescribeRole.Definition),
            Node("endpoint-result", "result", "Coincidence at maximal correlation one", ClaimBody(),
                "Compressing to the marginal supports preserves the geometric feasible values. At geometric correlation one, a centered fixed vector gives a nontrivial projection commuting with the marginal state. A partner projection has the same marginal and joint probability p, with 0 < p < 1. Centering both projections and dividing by sqrt(p(1-p)) gives arithmetic correlation one. The arithmetic Cauchy–Schwarz bound supplies the matching upper bound.", false, DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula formula, string prose, bool literature, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula ClaimBody() => FiniteTypes(All("rho", MatrixOf(Product(X("a"), X("b"))),
        Imp(Call("Matrix.PosSemidef", X("rho")), Imp(Eqn(Call("Matrix.trace", X("rho")), D(1)),
            Imp(Eqn(Call("muGM", X("rho")), D(1)), Eqn(Call("muAM", X("rho")), D(1)))))));
    private static Formula ValuesDefinition()
    {
        var rho = X("rho"); var x = X("X"); var y = X("Y");
        var ra = Seq(LambdaLower, Sp, X("i"), Sp, X("j"), Sp, Mapsto, Sp,
            Sum, Sp, Seq(X("k"), Colon, X("b")), Comma, Sp, Call("rho", Pair(X("i"), X("k")), Pair(X("j"), X("k"))));
        var rb = Seq(LambdaLower, Sp, X("k"), Sp, X("l"), Sp, Mapsto, Sp,
            Sum, Sp, Seq(X("i"), Colon, X("a")), Comma, Sp, Call("rho", Pair(X("i"), X("k")), Pair(X("i"), X("l"))));
        var objective = Eqn(X("r"), Norm(Call("Matrix.trace", Mul(Call("Matrix.kroneckerMap", Multiplication(), x, Call("Matrix.conjTranspose", y)), rho))));
        var normY = Eqn(Call("Matrix.trace", Mul(Call("Matrix.conjTranspose", y), Call("J", rb, y))), D(1));
        var normX = Eqn(Call("Matrix.trace", Mul(Call("Matrix.conjTranspose", x), Call("J", ra, x))), D(1));
        var centerY = Eqn(Call("Matrix.trace", Mul(Call("Matrix.of", rb), y)), D(0));
        var centerX = Eqn(Call("Matrix.trace", Mul(Call("Matrix.of", ra), x)), D(0));
        var conditions = And(Call("Matrix.IsHermitian", x), And(Call("Matrix.IsHermitian", y),
            And(centerX, And(centerY, And(normX, And(normY, objective))))));
        var body = Ex("X", MatrixOf(X("a")), Ex("Y", MatrixOf(X("b")), conditions));
        return FiniteTypes(All("J", MetricType(), All("rho", MatrixOf(Product(X("a"), X("b"))),
            Eqn(Call("correlationValues", X("J"), rho), Seq(OpenBrace, X("r"), Colon, Real(), Mid, body, CloseBrace)))));
    }
    private static Formula CoefficientDefinition(string name, Formula map) => FiniteTypes(All("rho", MatrixOf(Product(X("a"), X("b"))),
        Eqn(Call(name, X("rho")), Call("sSup", Call("correlationValues", map, X("rho"))))));
    private static Formula MetricType() => All("c", Q("Type"), Seq(Instances("c"),
        Arrow(MatrixOf(X("c")), Arrow(MatrixOf(X("c")), MatrixOf(X("c"))))));
    private static Formula ArithmeticMap() => MetricLambda(Seq(Parenthesized(Seq(new Formula.Fraction(D(1), D(2)), Colon, Complex())), Cdot,
        Parenthesized(Add(Mul(X("sigma"), X("Y")), Mul(X("Y"), X("sigma"))))));
    private static Formula GeometricMap() => MetricLambda(Mul(Mul(Call("CFC.sqrt", X("sigma")), X("Y")), Call("CFC.sqrt", X("sigma"))));
    private static Formula MetricLambda(Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(X("c"), Colon, Q("Type"))), Sp,
        Instances("c"), Sp, Parenthesized(Seq(X("sigma"), Sp, X("Y"), Colon, MatrixOf(X("c")))), Sp, Mapsto, Sp, body);
    private static Formula FiniteTypes(Formula body) => All("a", Q("Type"), All("b", Q("Type"), Seq(Instances("a"), Sp, Instances("b"), Sp, body)));
    private static Formula Instances(string s) => Seq(OpenBracket, Call("Fintype", X(s)), CloseBracket, Sp, OpenBracket, Call("DecidableEq", X(s)), CloseBracket);
    private static Formula MatrixOf(Formula n) => Call("Matrix", n, n, Complex());
    private static Formula Multiplication() => Seq(LambdaLower, Sp, X("x"), Sp, X("y"), Sp, Mapsto, Sp, Mul(X("x"), X("y")));
    private static Formula Q(string s)
    {
        var tokens = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(X(part));
        }
        return Seq(Operatorname, Sp, Grp(Seq([.. tokens])));
    }
    private static Formula X(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [.. xs]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string s, Formula t, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(s), Colon, t)), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string s, Formula t, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(X(s), Colon, t)), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), To, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Times, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula Norm(Formula a) => Seq(Vert, a, Vert);
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
}
