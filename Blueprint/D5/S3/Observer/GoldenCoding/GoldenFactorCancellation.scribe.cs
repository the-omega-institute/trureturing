using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenFactorCancellationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenFactorCancellation."
            + "golden_factor_cancellation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-normalized real involutions multiply to the standard complex structure.",
        H("Golden Factor Cancellation"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-factor-cancellation"),
            DeclarationHandle.Create(Declaration),
            H("The golden normalization cancels in the completed phase"),
            StatementSource.FromAuthor(CancellationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two real matrices are the source's explicit polarization factors. "
                        + "Their common denominator is two phi minus one, which equals the "
                        + "positive square root of five.")),
                Paragraph(Text(
                    "Direct matrix multiplication proves that both factors are involutions. "
                        + "Their ordered product is the standard integer-entry complex "
                        + "structure, while reversing the order changes its sign.")),
                Paragraph(Text(
                    "The completed matrix squares to minus the identity. Its displayed "
                        + "entries no longer contain the golden normalization carried by "
                        + "the two factors."))),
            DescribeRole.Theorem))));

    private static Formula CancellationFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula finTwo = Call("Fin", D(2));
        Formula matrixType = Call("Matrix", finTwo, finTwo, real);
        Formula phiNormalization = Subtract(Multiply(D(2), Varphi), D(1));
        Formula inverseNormalization = Call("inv", phiNormalization);
        Formula s = F.Id("S");
        Formula c = F.Id("C");
        Formula j = F.Id("J");
        Formula identity = F.Id("I");
        Formula sLiteral = Call("matrix2", D(1), D(2), D(2), Seq(Minus, D(1)));
        Formula cLiteral = Call(
            "matrix2", D(2), Seq(Minus, D(1)), Seq(Minus, D(1)), Seq(Minus, D(2)));
        Formula jLiteral = Call("matrix2", D(0), Seq(Minus, D(1)), D(1), D(0));

        return Disp(new Formula.Aligned([
            Seq(
                F.Id("let"), Sp, s, Colon, Sp, matrixType, Sp, Eq, Sp,
                Call("smul", inverseNormalization, sLiteral), Semi),
            Seq(
                Grp(), F.Id("let"), Sp, c, Colon, Sp, matrixType, Sp, Eq, Sp,
                Call("smul", inverseNormalization, cLiteral), Semi),
            Seq(
                Grp(), F.Id("let"), Sp, j, Colon, Sp, matrixType, Sp, Eq, Sp,
                jLiteral, Semi),
            Seq(
                Grp(), new Formula.Power(s, D(2)), Sp, Eq, Sp, identity,
                Sp, Land, Sp, new Formula.Power(c, D(2)), Sp, Eq, Sp, identity,
                Sp, Land),
            Seq(
                Grp(), Multiply(s, c), Sp, Eq, Sp, j, Sp, Land, Sp,
                Multiply(c, s), Sp, Eq, Sp, Seq(Minus, j), Sp, Land),
            Seq(
                Grp(), new Formula.Power(j, D(2)), Sp, Eq, Sp,
                Seq(Minus, identity), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
