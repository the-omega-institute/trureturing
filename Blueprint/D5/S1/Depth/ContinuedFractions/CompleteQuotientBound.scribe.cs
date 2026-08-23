using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class CompleteQuotientBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Mobius pullback scales a quadratic discriminant by the square of its determinant, so unimodular transfers preserve it.",
        H("Discriminants Under Mobius Pullback"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mobius-pullback-scales-the-discriminant"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.pullback_discriminant"),
                H("Mobius pullback scales the discriminant"),
                StatementSource.FromAuthor(PullbackDiscriminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pullback coefficients result from substituting the inverse "
                        + "linear-fractional relation and clearing its squared denominator. "
                        + "Their discriminant is the original discriminant multiplied by the "
                        + "square of the transfer determinant."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("unimodular-mobius-transfer-preserves-the-discriminant"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/CompleteQuotientBound."
                    + "unimodular_transform_preserves_discriminant"),
                H("Unimodular Mobius transfer preserves the discriminant"),
                StatementSource.FromAuthor(UnimodularDiscriminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A unimodular integer Mobius transfer has determinant one or minus one. "
                        + "Its determinant square is therefore one, so the pullback leaves the "
                        + "quadratic discriminant unchanged."))),
                DescribeRole.Theorem))));

    private static Formula PullbackDiscriminantFormula()
    {
        Formula coefficients = F.Id("f");
        Formula matrix = F.Id("M");

        return Disp(Seq(
            Forall, Sp, coefficients, Colon, Sp, QuadraticCoefficientTriples(),
            Comma, Sp, matrix, Colon, Sp, MobiusTransfers(), Comma, Esc,
            Discriminant(Pullback(coefficients, matrix)), Sp, Eq, Sp,
            Determinant(matrix), Caret, Grp(D(2)), Sp, Cdot, Sp,
            Discriminant(coefficients), Dot));
    }

    private static Formula UnimodularDiscriminantFormula()
    {
        Formula coefficients = F.Id("f");
        Formula matrix = F.Id("M");

        return Disp(Seq(
            Forall, Sp, coefficients, Colon, Sp, QuadraticCoefficientTriples(),
            Comma, Sp, matrix, Colon, Sp, MobiusTransfers(), Comma, Esc,
            Open,
            Determinant(matrix), Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            Determinant(matrix), Sp, Eq, Sp, Minus, D(1),
            Close, Sp, Rightarrow, Sp,
            Discriminant(Pullback(coefficients, matrix)), Sp, Eq, Sp,
            Discriminant(coefficients), Dot));
    }

    private static Formula QuadraticCoefficientTriples() =>
        Seq(Operatorname, Grp(F.Id("QuadraticCoefficients")));

    private static Formula MobiusTransfers() =>
        Seq(Operatorname, Grp(F.Id("MobiusInt")));

    private static Formula Pullback(Formula coefficients, Formula matrix) =>
        Call("pullback", coefficients, matrix);

    private static Formula Discriminant(Formula coefficients) =>
        Call("discriminant", coefficients);

    private static Formula Determinant(Formula matrix) => Call("det", matrix);
}
