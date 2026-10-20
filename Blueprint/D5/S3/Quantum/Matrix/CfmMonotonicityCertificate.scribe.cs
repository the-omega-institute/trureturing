using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CfmMonotonicityCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar rational function agrees with its matrix expression under functional calculus.",
        H("The rational functional-calculus expression"),
        Blocks(
            Entry("scalar-function", "scalarFunction", "The scalar rational counterexample",
                Disp(Eq(Call("scalarFunction", V("t")),
                    Sub(Add(Frac(Add(V("t"), Num(1)), Add(V("t"), Num(3))),
                        Frac(Add(V("t"), Num(1)), Add(Mul(Num(2), V("t")), Num(4)))),
                        Mul(Frac(Num(1), Num(20000)),
                            Frac(Add(V("t"), Num(1)), Add(Mul(Num(3), V("t")), Num(5))))))),
                "scalarFunction t = (t+1)/(t+3) + (t+1)/(2t+4) - (1/20000)(t+1)/(3t+5). Its total real extension is used by continuous functional calculus; all matrix inputs have strictly positive spectrum.", true),
            Entry("rational-function", "rationalFunction", "Rational matrix expression",
                Disp(Eq(Call("rationalFunction", V("A")),
                    Sub(Add(Mul(Add(V("A"), Num(1)), Inv(Add(V("A"), Num(3)))),
                        Mul(Add(V("A"), Num(1)), Inv(Add(Smul(Num(2), V("A")), Num(4))))),
                        Smul(Frac(Num(1), Num(20000)),
                            Mul(Add(V("A"), Num(1)), Inv(Add(Smul(Num(3), V("A")), Num(5)))))))),
                "For a complex square matrix of any finite size, rationalFunction A is (A+I)(A+3I) inverse plus (A+I)(2A+4I) inverse minus (1/20000) times (A+I)(3A+5I) inverse. Every scalar multiplication in the Lean definition uses the real scalar action. The inverse is Mathlib's nonsingular matrix inverse.", true),
            Entry("lower-matrix", "lowerMatrix", "The diagonal lower endpoint",
                Disp(Eq(V("lowerMatrix"), Call("diagonal", Tuple(Frac(Num(1), Num(3)), Num(1), Num(3))))),
                "lowerMatrix is the complex Hermitian 3 by 3 diagonal matrix with diagonal 1/3, 1, 3.", true),
            Entry("upper-matrix", "upperMatrix", "The upper endpoint",
                Disp(Eq(Smul(Num(25), V("upperMatrix")),
                    Call("rows", Tuple(Num(11), Num(4), Num(8)),
                        Tuple(Num(4), Num(31), Num(12)), Tuple(Num(8), Num(12), Num(99))))),
                "upperMatrix is 1/25 times the symmetric matrix whose rows are (11,4,8), (4,31,12), (8,12,99), regarded as a complex Hermitian matrix.", true),
            Entry("test-vector", "testVector", "The separating vector",
                Disp(Eq(V("testVector"), Tuple(Negate(Num(35)), Num(48), Negate(Num(15))))),
                "testVector is the complex column vector (-35,48,-15).", true),
            Entry("quadratic-readout", "quadraticReadout", "Real quadratic form",
                Disp(Eq(Call("quadraticReadout", V("X")),
                    Call("Re", Mul(Call("adjoint", V("testVector")), Mul(V("X"), V("testVector")))))),
                "quadraticReadout X is the real part of the conjugate-transpose quadratic form testVector adjoint times X times testVector. It is defined on every complex 3 by 3 matrix.", true),
            Entry("cfc-rational-function", "cfc_rationalFunction", "Functional calculus of the rational function",
                Disp(All("n", V("Nat"), All("A", Call("ComplexSquareMatrix", V("n")),
                    Imp(Call("PosDef", V("A")),
                        Eq(Call("cfc", V("scalarFunction"), V("A")), Call("rationalFunction", V("A"))))))),
                "For every natural number n and every positive definite complex n by n matrix A, cfc scalarFunction A equals rationalFunction A. The spectrum is finite, so all scalar functions are continuous there. Its nonnegative spectrum makes all three affine denominators strictly positive. cfc_map_div, cfc_add_const and cfc_const_mul_id identify each rational term with its matrix counterpart; Matrix.nonsing_inv_eq_ringInverse identifies the two inverse conventions.", false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Inv(Formula x) => new Formula.Power(x, Negate(Num(1)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Negate(Formula x) => Seq(Minus, x);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Tuple(params Formula[] xs) => Seq(Open, Seq(xs.SelectMany((x, i) =>
        i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, V(name), Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
