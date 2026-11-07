using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Riemannian;

internal sealed class ZimmermannStoyeCodimensionOneCurvatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Geometry/zimmermannstoye2024stiefel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp codimension-one Euclidean Stiefel curvature bounds and endpoints.",
        H("Zimmermann--Stoye Conjecture 1"),
        Blocks(
            Node("stiefel", "The Stiefel set", Stiefel(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "The Stiefel manifold is St(n,p) = {U ∈ ℝⁿˣᵖ | UᵀU = Iₚ}. (Notational specifics, PDF page 2.) The matrix equation uses real matrices and the identity matrix of size p."),
            Node("orthonormalTangentBlocks", "Orthonormal tangent blocks", TangentBlocks(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "The source states: “The matrices X,Y form a (Riemannian) ONB if and only if 1 = ‖Aᵢ‖²_F + ‖Bᵢ‖²_F, i=1,2, 0 = tr(A₁ᵀA₂) + tr(B₁ᵀB₂).” (Section 3.3, PDF page 15.) Its tangent representation has Aᵢᵀ = −Aᵢ. The five equations express these two skew conditions and the three orthonormality equations, with real p by p top blocks and real q by p bottom blocks."),
            Node("euclideanSectionalCurvature", "The Euclidean curvature expression", Curvature(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "Equation (26) gives the Euclidean sectional curvature on an orthonormal tangent pair. Matrix norms are Frobenius norms, and the commutator is A₁A₂−A₂A₁. The orthogonal base-point isometry identifies every tangent plane with these blocks; this identification is the source's geometric interpretation of the matrix expression."),
            Node("claim", "The conjectured sharp interval", Equal(Call("claim"), ClaimBody()), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                "The source states: “For n ≥ 4 and (n, p) = (n, n − 1), sharp bounds on the sectional curvature of the Stiefel manifold under the Euclidean metric are −1/2 ≤ K_e^St(X,Y) ≤ 1/2.” (Conjecture 1, PDF page 17.) Here p=n−1, the bottom blocks have one row, and sharpness means that each endpoint is attained in every such dimension."),
            Node("result", "The sharp interval and both endpoints", ClaimBody(), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                "The row Gram matrix is diagonalized by an orthogonal change of the tangent-plane basis. A second orthogonal change puts the rows on distinct coordinate axes. The curvature expansion preserves the coupled cross term; the real skew commutator estimate and a scalar two-square deficit give the interval. Fixed coordinate patterns attain both endpoints in every target dimension.")),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("zimmermann-stoye-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Call("Nat");
    private static Formula R => Call("Real");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula columns) => Call("Matrix", Fin(rows), Fin(columns), R);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(part));
        }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return arguments.Length == 0 ? head : new Formula.Apply(head, [.. arguments]);
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negative(Formula a) => new Formula.Negate(a);
    private static Formula Fraction(int a, int b) => new Formula.Fraction(Num(a), Num(b));
    private static Formula Square(Formula a) => new Formula.Power(a, Num(2));
    private static Formula NormSquare(Formula a) => Square(new Formula.Norm(a));
    private static Formula Transpose(Formula a) => Call("Matrix.transpose", a);
    private static Formula Trace(Formula a) => Call("Matrix.trace", a);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All((string name, Formula type)[] binders, Formula body) => Bind(FormulaQuantifier.ForAll, binders, body);
    private static Formula Exists((string name, Formula type)[] binders, Formula body) => Bind(FormulaQuantifier.Exists, binders, body);
    private static Formula Bind(FormulaQuantifier quantifier, (string name, Formula type)[] binders, Formula body)
    {
        for (var i = binders.Length - 1; i >= 0; i--)
            body = new Formula.Bind(quantifier, FormulaIdentifier.Create(binders[i].name), binders[i].type, body);
        return body;
    }
    private static Formula Stiefel()
    {
        var n = V("n"); var p = V("p"); var u = V("U");
        var set = Call("setOf", Seq(Call("fun"), Sp, Parenthesized(Seq(u, Colon, Sp, Matrix(n, p))), Sp, Mapsto, Sp,
            Equal(Mul(Transpose(u), u), Num(1))));
        return All([("n", N), ("p", N)], Equal(Call("stiefel", n, p), set));
    }
    private static Formula TangentBlocks()
    {
        var p = V("p"); var q = V("q"); var a = V("A1"); var c = V("A2"); var b = V("B1"); var d = V("B2");
        var body = And(Equal(Transpose(a), Negative(a)), And(Equal(Transpose(c), Negative(c)),
            And(Equal(Add(NormSquare(a), NormSquare(b)), Num(1)),
            And(Equal(Add(NormSquare(c), NormSquare(d)), Num(1)),
                Equal(Add(Trace(Mul(Transpose(a), c)), Trace(Mul(Transpose(b), d))), Num(0))))));
        return All([("p", N), ("q", N), ("A1", Matrix(p, p)), ("A2", Matrix(p, p)), ("B1", Matrix(q, p)), ("B2", Matrix(q, p))],
            Equal(Call("orthonormalTangentBlocks", a, c, b, d), body));
    }
    private static Formula Curvature()
    {
        var p = V("p"); var q = V("q"); var a = V("A1"); var c = V("A2"); var b = V("B1"); var d = V("B2");
        var first = NormSquare(Sub(Mul(b, c), Mul(d, a)));
        var second = Mul(Fraction(1, 2), NormSquare(Sub(Mul(b, Transpose(d)), Mul(d, Transpose(b)))));
        var third = Mul(Fraction(1, 2), NormSquare(Sub(Mul(Transpose(b), d), Mul(Transpose(d), b))));
        var fourth = Mul(Fraction(1, 4), NormSquare(Sub(Sub(Mul(a, c), Mul(c, a)), Sub(Mul(Transpose(d), b), Mul(Transpose(b), d)))));
        return All([("p", N), ("q", N), ("A1", Matrix(p, p)), ("A2", Matrix(p, p)), ("B1", Matrix(q, p)), ("B2", Matrix(q, p))],
            Equal(Call("euclideanSectionalCurvature", a, c, b, d), Add(Sub(Add(first, second), third), fourth)));
    }
    private static Formula ClaimBody()
    {
        var n = V("n"); var p = Sub(n, Num(1));
        var a = V("A1"); var c = V("A2"); var b = V("B1"); var d = V("B2");
        (string name, Formula type)[] blocks = [("A1", Matrix(p, p)), ("A2", Matrix(p, p)), ("B1", Matrix(Num(1), p)), ("B2", Matrix(Num(1), p))];
        var hypotheses = Call("orthonormalTangentBlocks", a, c, b, d);
        var curvature = Call("euclideanSectionalCurvature", a, c, b, d);
        var half = Fraction(1, 2);
        var bounds = All(blocks, Implies(hypotheses, And(Le(Negative(half), curvature), Le(curvature, half))));
        var lower = Exists(blocks, And(hypotheses, Equal(curvature, Negative(half))));
        var upper = Exists(blocks, And(hypotheses, Equal(curvature, half)));
        return All([("n", N)], Implies(Le(Num(4), n), And(bounds, And(lower, upper))));
    }
}
