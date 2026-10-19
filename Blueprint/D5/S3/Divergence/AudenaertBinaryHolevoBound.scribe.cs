using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class AudenaertBinaryHolevoBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Holevo information in bits is at most half the trace norm of the difference.",
        H("Audenaert's binary Holevo bound"),
        Blocks(Describe.Lean(DescribeId.Create("audenaert-binary-holevo"),
            DeclarationHandle.Create("D5/S3/Divergence/AudenaertBinaryHolevoBound.binaryHolevoBound"),
            H("The binary ensemble inequality"), StatementSource.FromAuthor(Bound()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/audenaert2014skew")),
            Blocks(Paragraph(Text("Audenaert, Quantum Skew Divergence, Theorem 14, bounds Holevo information by the classical mixing entropy times the maximal trace distance. For an equiprobable binary ensemble the mixing entropy is one bit. The matrices may be singular. The matrix-log resolvent integral gives the derivative along a positive affine path. Positivity of that derivative and its trace pairing bound the skew divergence by trace distance times the negative logarithm of the mixing weight. Specializing the weight to one half gives the binary inequality for strictly positive states. Adding epsilon times the identity and dividing by one plus n epsilon preserves trace one, and continuity of x log x extends the estimate to singular states."))),
            DescribeRole.Theorem))));
    private static Formula V(string n) => F.Id(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(V(a)), Dot, Operatorname, Grp(V(b)));
    private static Formula App(Formula f, params Formula[] a) => Seq(f, Sp, Parenthesized(Seq(a.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Seq(Comma, Sp), x }).ToArray())));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Half(Formula a) => new Formula.Fraction(a, D(2));
    private static Formula Scale(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Lam(string n, Formula t, Formula b) => Parenthesized(Seq(Parenthesized(Seq(V(n), Colon, Sp, t)), Sp, Mapsto, Sp, b));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin => Call("Fin", V("n"));
    private static Formula Mat => Call("Matrix", Fin, Fin, Complex);
    private static Formula Entropy(Formula a) => Seq(Minus, Sp, Call("re", Call("trace", Call("cfc",
        Lam("x", Real, Mul(V("x"), App(Q("Real", "logb"), D(2), V("x")))), a))));

    private static Formula State(Formula a) => And(Call("PosSemidef", a), Eq(Call("trace", a), D(1)));
    private static Formula Bound()
    {
        var s = V("sigma"); var t = V("tau");
        var halfComplex = Seq(Half(D(1)), Colon, Sp, Complex);
        var left = Sub(Entropy(Scale(halfComplex, Add(s, t))), Half(Add(Entropy(s), Entropy(t))));
        return Disp(All("n", Nat, All("sigma", Mat, All("tau", Mat,
            Imp(State(s), Imp(State(t), Le(left, Half(Call("traceNorm", Sub(s, t))))))))));
    }
}
