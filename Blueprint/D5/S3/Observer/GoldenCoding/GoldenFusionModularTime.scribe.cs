using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenFusionModularTimeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenFusionModularTime."
            + "golden_fusion_modular_time";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared Fibonacci fusion matrix has reciprocal golden spectrum and a reflected logarithmic generator.",
        H("Golden Fusion Modular Time"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-fusion-modular-time"),
            DeclarationHandle.Create(Declaration),
            H("Golden fusion becomes reciprocal logarithmic time in its eigenbasis"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source convention is F=(0,1;1,1). Direct finite arithmetic gives "
                        + "det(F)=-1 and Delta=F^2=(1,1;1,2) with determinant one. Its "
                        + "quadratic form is (x+y)^2+y^2, so the square is positive definite.")),
                Paragraph(Text(
                    "The displayed vectors are explicit eigenvectors with eigenvalues phi^2 "
                        + "and phi^(-2). Positivity of phi^2 makes the reciprocal diagonal "
                        + "spectrum positive definite and prevents totalized inversion or "
                        + "logarithm at zero.")),
                Paragraph(Text(
                    "In the eigenbasis, K is the diagonal spectral logarithm. The laws for "
                        + "logarithms of powers and inverses identify its entries as opposite, "
                        + "and direct multiplication by the eigenline swap J proves both "
                        + "J Delta J=Delta^(-1) and J K J=-K."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula phi = Varphi;
        Formula phiSquared = Seq(phi, Caret, Grp(D(2)));
        Formula phiInverseSquared = Seq(phi, Caret, Grp(Minus, D(2)));
        Formula fibonacci = F.Id("F");
        Formula delta = F.Id("Delta");
        Formula eigenDelta = Seq(delta, Underscore, Grp(F.Id("eig")));
        Formula generator = F.Id("K");
        Formula swap = F.Id("J");
        Formula plusVector = F.Id("v_plus");
        Formula minusVector = F.Id("v_minus");
        Formula fibonacciLiteral = Call("matrix2", D(0), D(1), D(1), D(1));
        Formula squareLiteral = Call("matrix2", D(1), D(1), D(1), D(2));

        Formula definitions = Seq(
            F.Id("let"), Sp, fibonacci, Sp, Colon, Eq, Sp, fibonacciLiteral, Comma, Sp,
            delta, Sp, Colon, Eq, Sp, fibonacci, Caret, Grp(D(2)), Comma);
        Formula algebraicData = Seq(
            Call("det", fibonacci), Sp, Eq, Sp, Minus, D(1), Sp, Land, Sp,
            delta, Sp, Eq, Sp, squareLiteral, Sp, Land, Sp,
            Call("det", delta), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("PosDef", delta));
        Formula eigenpairs = Seq(
            Call("mulVec", delta, plusVector), Sp, Eq, Sp,
            phiSquared, plusVector, Sp, Land, Sp,
            Call("mulVec", delta, minusVector), Sp, Eq, Sp,
            phiInverseSquared, minusVector);
        Formula modularData = Seq(
            Call("PosDef", eigenDelta), Sp, Land, Sp,
            generator, Sp, Eq, Sp, Call("spectralLog", eigenDelta), Sp, Land, Sp,
            swap, eigenDelta, swap, Sp, Eq, Sp, Seq(eigenDelta, Caret, Grp(Minus, D(1))),
            Sp, Land, Sp, swap, generator, swap, Sp, Eq, Sp, Minus, generator,
            Sp, Land, Sp, generator, Sp, Neq, Sp, D(0));

        return Disp(new Formula.Aligned([
            definitions,
            Seq(Grp(), algebraicData, Sp, Land),
            Seq(Grp(), eigenpairs, Sp, Land),
            Seq(Grp(), modularData, Dot),
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
