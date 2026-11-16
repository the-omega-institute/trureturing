using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class SemidefiniteCoefficientKernelCheckDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Algebra/SemidefiniteCoefficientKernelCheck.";

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Matrix(Formula m, Formula n) =>
        Call("Matrix", Call("Fin", m), Call("Fin", n), Call("Complex"));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And,
            Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies,
            Seq(Open, b, Close));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, type)), Sp,
            Parenthesized(body));
    private static Formula Phi(Formula X, Formula T, Formula k) =>
        SumOver("r", Call("Fin", k), SumOver("s", Call("Fin", k),
            Smul(Call("entry", T, V("r"), V("s")),
                Mul(Call("conjTranspose", Call("entry", X, V("r"))),
                    Call("entry", X, V("s"))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive semidefinite coefficient matrix is detected by its matrix-valued Gram compression on a complex-linearly independent family.",
        H("Positive semidefinite coefficient-kernel exclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-semidefinite-coefficient-kernel"),
                DeclarationHandle.Create(Prefix + "exact_check"),
                H("The coefficient map has trivial positive-semidefinite kernel"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary natural a, b and k, X is a family of a by b complex matrices " +
                        "indexed by Fin k and is complex-linearly independent. For a positive semidefinite " +
                        "k by k complex matrix T, form Phi(T) as the finite double sum of T r s times " +
                        "the conjugate-transpose Gram block X r star times X s. If Phi(T) is zero, then T " +
                        "is zero. The statement includes k = 0, a = 0 and b = 0.")),
                    Paragraph(Text(
                        "The proof evaluates each diagonal entry of Phi(T), reindexes the finite sums, " +
                        "and applies Matrix.PosSemidef.dotProduct_mulVec_zero_iff after the nonnegative " +
                        "summands are shown to sum to zero. The resulting coefficient relation is exactly " +
                        "the finite-type characterization of complex linear independence. No scalar-Gram " +
                        "premise and no positivity assumption on a, b or k is used."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = V("a"), b = V("b"), k = V("k"), X = V("X"), T = V("T");
        Formula premises = And(Call("LinearIndependent", Complex(), X),
            Call("PosSemidef", T));
        Formula conclusion = Imp(premises,
            Imp(Eq(Phi(X, T, k), D(0)), Eq(T, D(0))));
        return All("a", Nat(), All("b", Nat(), All("k", Nat(),
            All("X", Arr(Call("Fin", k), Matrix(a, b)),
                All("T", Matrix(k, k), conclusion)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Nat() => F.Id("Nat");
    private static Formula Complex() => F.Id("Complex");
}
