using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenModularStandardPairDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenModularStandardPair."
            + "golden_modular_standard_pair";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden modular step squares to a positive definite unimodular operator "
            + "with reciprocal golden scales.",
        H("Golden Modular Standard Pair"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-modular-standard-pair"),
            DeclarationHandle.Create(Declaration),
            H("The golden first phase forms a finite-dimensional standard pair"),
            StatementSource.FromAuthor(StandardPairFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The one-step matrix F has rows (0,1) and (1,1). Direct finite "
                        + "matrix multiplication identifies its square Delta_phi with "
                        + "the matrix having rows (1,1) and (1,2).")),
                Paragraph(Text(
                    "The squared operator has determinant one and trace three. Its "
                        + "quadratic form is (x_0+x_1)^2+x_1^2, so every nonzero real "
                        + "vector has strictly positive value.")),
                Paragraph(Text(
                    "The vectors (1,0) and (1,-1) both give quadratic-form value one. "
                        + "The squared golden ratio and its reciprocal square likewise "
                        + "have product one and sum three."))),
            DescribeRole.Theorem))));

    private static Formula StandardPairFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula finTwo = Call("Fin", D(2));
        Formula matrixType = Call("Matrix", finTwo, finTwo, real);
        Formula fibonacci = F.Id("F");
        Formula delta = new Formula.Subscript(
            F.Id("Delta"),
            new Formula.LatexMacro(FormulaLatexMacro.Phi));
        Formula fibonacciLiteral = Call("matrix2", D(0), D(1), D(1), D(1));
        Formula deltaLiteral = Call("matrix2", D(1), D(1), D(1), D(2));
        Formula eZero = Call("vector2", D(1), D(0));
        Formula eAnti = Call("vector2", D(1), Seq(Minus, D(1)));
        Formula phiSquared = new Formula.Power(Varphi, D(2));
        Formula inversePhiSquared = Call("inv", phiSquared);

        return Disp(new Formula.Aligned([
            Seq(
                F.Id("let"), Sp, fibonacci, Colon, Sp, matrixType, Sp, Eq, Sp,
                fibonacciLiteral, Semi),
            Seq(
                F.Id("let"), Sp, delta, Colon, Sp, matrixType, Sp, Eq, Sp,
                new Formula.Power(fibonacci, D(2)), Semi),
            Seq(
                new Formula.Power(fibonacci, D(2)), Sp, Eq, Sp, deltaLiteral,
                Sp, Land),
            Seq(
                Call("det", delta), Sp, Eq, Sp, D(1), Sp, Land,
                Sp, Call("trace", delta), Sp, Eq, Sp, D(3), Sp, Land),
            Seq(
                Call("PosDef", delta), Sp, Land,
                Sp, Call("quadraticValue", delta, eZero), Sp, Eq, Sp, D(1),
                Sp, Land),
            Seq(
                Call("quadraticValue", delta, eAnti), Sp, Eq, Sp, D(1),
                Sp, Land),
            Seq(
                phiSquared, Sp, Cdot, Sp, inversePhiSquared, Sp, Eq, Sp, D(1),
                Sp, Land),
            Seq(
                phiSquared, Sp, Plus, Sp, inversePhiSquared, Sp, Eq, Sp, D(3),
                Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
