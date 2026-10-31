using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.PauliFunding;

internal sealed class ParityTraceComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison.";
    private static Formula X(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula Mat => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), R);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Call(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula W => X("W");
    private static Formula A => X("alpha");
    private static Formula B => X("beta");
    private static Formula C => X("c");
    private static Formula J => X("j");
    private static Formula Poly => Sub(Sub(Pow(C,D(2)), Mul(Mul(D(2),A),C)),B);
    private static Formula Tr => Call("trace", Pow(W,Mul(D(2),J)));
    private static Formula Vieta => And(Eqn(Call("trace",W),Mul(D(2),A)), Eqn(Call("det",W),Sub(D(0),B)));
    private static Formula Bind(Formula body) => All("W",Mat,All("alpha",R,All("beta",R,body)));
    private static Formula FormulaStatement() => Bind(Imp(And(Le(D(0),B),Vieta),
        All("j",N,Eqn(Tr,Call("evenMoment",A,B,J)))));
    private static Formula ComparisonStatement(bool strict) => Bind(All("c",R,
        Imp(And(And(Le(D(0),A),Le(D(0),B)),And(Le(D(0),C),Vieta)),
            Imp(strict ? Lt(Poly,D(0)) : Le(Poly,D(0)),All("j",N,
                strict ? Imp(Le(D(1),J),Lt(Pow(C,Mul(D(2),J)),Tr)) : Le(Pow(C,Mul(D(2),J)),Tr))))));
    private static DocumentBlock Node(string id, string title, string decl, Formula f, string text) =>
        Describe.Lean(DescribeId.Create("parity-trace-"+id),DeclarationHandle.Create(Prefix+decl),H(title),
            StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic characteristic roots compare every even power trace of a real two by two matrix.",
        H("Even matrix traces and quadratic comparison"),Blocks(
            Paragraph(Text("Write evenMoment(alpha,beta,j)=(alpha+sqrt(alpha^2+beta))^(2j)+(alpha-sqrt(alpha^2+beta))^(2j), with the nonnegative real square root. The matrix W is arbitrary: symmetry, positivity and invertibility are not required. The parity control matrix is diag(1,-1).")),
            Node("formula","Vieta power traces","even_trace_formula",FormulaStatement(),
                "Nonnegative beta makes the characteristic roots real. Their sum and product are the supplied trace and determinant. The existing ring-general MatrixTracePowerSum.trace_pow_eq_add_pow then gives the identity, including beta=0 and repeated roots."),
            Node("comparison","A lower quadratic comparison","even_trace_comparison",ComparisonStatement(false),
                "A nonnegative c in the sublevel set c^2-2 alpha c-beta≤0 lies below the positive characteristic root. Taking the even power preserves this order, while the other root contributes a nonnegative even power. The order j may be zero."),
            Node("strict","Strict comparison at every positive order","even_trace_strict",ComparisonStatement(true),
                "A strictly negative characteristic polynomial places c strictly below the positive root. For j≥1 this gives a strict even-power inequality. The result applies to the parity transform of actual Pauli control resolvents, whose product moments are even powers of W."))));
}
