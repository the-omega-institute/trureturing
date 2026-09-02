using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OffLineZeroNegativeTruncatedWeilSquareDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/OffLineZeroNegativeTruncatedWeilSquare."
            + "offLineZero_yields_negative_truncated_weil_square";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-line nonreal zero inside a symmetric cutoff separates the truncated Weil form.",
        H("Off-Line Zero Negative Truncated Weil Square"),
        Blocks(Describe.Lean(
            DescribeId.Create("off-line-zero-yields-negative-truncated-weil-square"),
            DeclarationHandle.Create(Declaration),
            H("A finite-cutoff separator from one off-line nonreal zero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Choose the lesser index in each reflection pair inside the symmetric "
                        + "cutoff. These representatives have distinct frequencies even up to "
                        + "sign, so finite even interpolation prescribes opposite unit values "
                        + "on the target conjugate pair and zero on every other pair.")),
                Paragraph(Text(
                    "The convolution-square summands outside the target four-point orbit then "
                        + "vanish. The frozen prescribed-pair orbit identity makes the remaining "
                        + "real sum minus four times the positive stored multiplicity.")),
                Paragraph(Text(
                    "This is only a finite-cutoff statement. It asserts nothing about limits, "
                        + "SymmetricConvergent, or zeroSum; the nonzero imaginary-part hypothesis "
                        + "is the explicit M3-d input."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula cutoff = F.Id("T");
        Formula test = F.Id("g");
        Formula zero = Call("zero", zeroData, index);
        Formula premises = And(
            Seq(index, Sp, InMacro, Sp, Call("symmetricIndices", zeroData, cutoff)),
            NotEqual(RealPart(zero), F.Id("criticalAbscissa")),
            NotEqual(ImaginaryPart(zero), D(0)));
        Formula truncated = Call(
            "truncatedZeroSum",
            zeroData,
            Call("convolutionSquare", test),
            cutoff);
        Formula conclusion = Seq(
            Exists, Sp, Bound(test, F.Id("WeilTestFunction")), Comma, Sp,
            RealPart(truncated), Sp, Lt, Sp, D(0));

        return Disp(Seq(
            Forall, Sp,
            Bound(zeroData, F.Id("ZeroData")), Comma, Sp,
            Bound(index, Naturals()), Comma, Sp,
            Bound(cutoff, Reals()), Comma, RowBreak, Grp(),
            ImpliesFormula(premises, conclusion), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var i = 1; i < clauses.Length; i++)
        {
            result = Seq(Open, result, Close, Sp, Land, Sp, Open, clauses[i], Close);
        }

        return result;
    }

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Sp, Open, value, Close);

    private static Formula ImpliesFormula(Formula premises, Formula conclusion) =>
        Seq(Open, premises, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
