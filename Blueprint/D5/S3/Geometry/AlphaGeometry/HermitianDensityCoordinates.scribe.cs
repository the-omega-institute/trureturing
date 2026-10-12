using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlphaGeometry;

internal sealed class HermitianDensityCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.";
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula n => F.Id("n");
    private static Formula x => F.Id("x");
    private static Formula A => F.Id("A");
    private static Formula k => F.Id("k");
    private static Formula row => F.Id("row");
    private static Formula col => F.Id("col");
    private static Formula r => F.Id("r");
    private static Formula s => F.Id("s");
    private static Formula FinN => Call("Fin", n);
    private static Formula Dim => Sub(Pow(n, D(2)), D(1));
    private static Formula Coord => Arrow(Call("Fin", Dim), R);
    private static Formula Mat => App(Op("Matrix"), FinN, FinN, C);
    private static Formula Herm(Formula v) => App(Q("Matrix", "IsHermitian"), v);
    private static Formula Pos(Formula v) => App(Q("Matrix", "PosDef"), v);
    private static Formula Trace(Formula v) => App(Q("Matrix", "trace"), v);
    private static Formula Val(Formula v) => Call("val", v);
    private static Formula Rho(Formula v) => Call("rho", v);
    private static Formula Chart(Formula v) => Call("chartPoint", v);
    private static Formula PositiveN => Less(D(0), n);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real coordinate chart for Hermitian trace-one matrices.", H("HermitianDensityCoordinates"), Blocks(
            Node("G", All(n, N, All(k, Call("Fin", Dim), Equal(Call("G", n, k),
                Fun(r, FinN, Fun(s, FinN,
                    Let(row, App(Q("Nat", "div"), Val(k), n),
                    Let(col, App(Q("Nat", "mod"), Val(k), n),
                    If(Equal(row, col),
                        Sub(If(And(Equal(Val(r), row), Equal(Val(s), row)), D(1), D(0)),
                            If(And(Equal(Val(r), Sub(n, D(1))), Equal(Val(s), Sub(n, D(1)))), D(1), D(0))),
                        If(Less(row, col),
                            If(Or(And(Equal(Val(r), row), Equal(Val(s), col)),
                                  And(Equal(Val(r), col), Equal(Val(s), row))), D(1), D(0)),
                            Sub(If(And(Equal(Val(r), row), Equal(Val(s), col)), Q("Complex", "I"), D(0)),
                                If(And(Equal(Val(r), col), Equal(Val(s), row)), Q("Complex", "I"), D(0)))))))))))),
                "The natural matrix-grid index omits the last diagonal position. Nat.div and Nat.mod are natural-number division and remainder. Diagonal directions subtract the final diagonal entry; the two ordered off-diagonal positions give the real and imaginary Hermitian directions.", DescribeRole.Definition),
            Node("rho", All(n, N, All(x, Coord, Equal(Rho(x),
                Add(Smul(new Formula.Fraction(D(1), Seq(n, Sp, Colon, Sp, R)), Seq(D(1), Sp, Colon, Sp, Mat)),
                    SumOver(k, Call("Fin", Dim), Smul(App(x, k), Call("G", n, k))))))),
                "The affine chart has trace-one center and traceless Hermitian coordinate directions. Scalar multiplication is over the real numbers.", DescribeRole.Definition),
            Node("chartPoint", All(n, N, All(A, Mat, Equal(Chart(A),
                Fun(k, Call("Fin", Dim),
                    Let(row, App(Q("Nat", "div"), Val(k), n),
                    Let(col, App(Q("Nat", "mod"), Val(k), n),
                    Seq(Op("if"), Sp, F.Id("h"), Sp, Colon, Sp, And(Less(row, n), Less(col, n)), Sp,
                        Op("then"), Sp, Parenthesized(
                            Let(F.Id("entry"), App(A,
                                Seq(Langle, Sp, row, Comma, Sp, F.Id("h"), Dot, D(1), Rangle),
                                Seq(Langle, Sp, col, Comma, Sp, F.Id("h"), Dot, D(2), Rangle)),
                                If(Equal(row, col),
                                    Sub(Seq(F.Id("entry"), Dot, Op("re")), new Formula.Fraction(D(1), Seq(n, Sp, Colon, Sp, R))),
                                    If(Less(row, col), Seq(F.Id("entry"), Dot, Op("re")), Seq(F.Id("entry"), Dot, Op("im")))))),
                        Sp, Op("else"), Sp, D(0)))))))),
                "The inverse chart reads the real upper entries, the imaginary lower entries, and the centered diagonal entries. The bound proof h supplies the two Fin indices. Nat.div and Nat.mod use natural-number division and remainder.", DescribeRole.Definition),
            Node("rho_isHermitian", All(n, N, All(x, Coord, Herm(Rho(x)))),
                "Every chart value is Hermitian.", DescribeRole.Theorem),
            Node("rho_trace", All(n, N, Imp(PositiveN, All(x, Coord, Equal(Trace(Rho(x)), D(1))))),
                "For positive matrix dimension the chart value has trace one.", DescribeRole.Theorem),
            Node("chart_left_inverse", All(n, N, Imp(PositiveN, All(x, Coord, Equal(Chart(Rho(x)), x)))),
                "Reading the coordinates of a chart value recovers every original coordinate.", DescribeRole.Theorem),
            Node("hermitian_trace_one_chart_equiv", All(n, N, Imp(PositiveN, All(A, Mat,
                Imp(Herm(A), Imp(Equal(Trace(A), D(1)), Equal(Rho(Chart(A)), A)))))),
                "Reconstructing a Hermitian trace-one matrix from its chart coordinates recovers the matrix. The final diagonal coordinate follows from the trace equation.", DescribeRole.Theorem),
            Node("hermitian_posdef_open", All(n, N, Call("IsOpen",
                SetOf(A, Seq(OpenBrace, A, Sp, Colon, Sp, Mat, Sp, Slash, Slash, Sp, Herm(A), CloseBrace), Pos(Val(A))))),
                "Positive definite matrices form an open set in the Hermitian subspace.", DescribeRole.Theorem),
            Node("positive_chart_open", All(n, N, Call("IsOpen", SetOf(x, Coord, Pos(Rho(x))))),
                "Positive definiteness is an open condition in the density coordinates.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hermitiandensitycoordinates-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Op(string v) => Seq(Operatorname, Grp(F.Id(v)));
    private static Formula Q(string a, string b) => Seq(Op(a), Dot, Op(b));
    private static Formula Call(string f, params Formula[] args) => App(Op(f), args);
    private static Formula Parenthesized(Formula v) => Seq(Open, v, Close);
    private static Formula All(Formula v, Formula t, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(v, Sp, Colon, Sp, t)), Comma, Sp, body);
    private static Formula Fun(Formula v, Formula t, Formula body) => Seq(Op("fun"), Sp, Parenthesized(Seq(v, Sp, Colon, Sp, t)), Sp, Mapsto, Sp, body);
    private static Formula Let(Formula v, Formula value, Formula body) => Seq(Op("let"), Sp, v, Sp, Colon, F.Eq, Sp, value, Semi, Sp, body);
    private static Formula If(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, Parenthesized(p), Sp, Op("then"), Sp, Parenthesized(a), Sp, Op("else"), Sp, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula SumOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Sum, Seq(v, Sp, Colon, Sp, t)), Sp, Parenthesized(body));
    private static Formula SetOf(Formula v, Formula t, Formula p) => Seq(OpenBrace, v, Sp, Colon, Sp, t, Sp, Mid, Sp, p, CloseBrace);
}
