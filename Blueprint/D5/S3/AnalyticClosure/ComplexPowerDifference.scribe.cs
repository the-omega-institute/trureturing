using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class ComplexPowerDifferenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On a complex disk of radius H, the difference of the ell-th powers is bounded "
            + "by ell times the distance of the bases times H^(ell-1).",
        H("Differences of complex powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("complex-power-difference-norm-bound"),
            DeclarationHandle.Create(
                "D5/S3/AnalyticClosure/ComplexPowerDifference.norm_pow_sub_pow_le"),
            H("Uniform power-difference bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let a and b be complex numbers, ell a natural number, and H a "
                    + "nonnegative real number bounding both norms. Factor a^ell-b^ell "
                    + "as a-b times a sum of ell mixed powers. Each summand has norm "
                    + "at most H^(ell-1), so the triangle inequality gives the bound. "
                    + "The exponent ell-1 uses truncated natural subtraction. "
                    + "For ell=0 the difference and the right side both vanish."))),
            DescribeRole.Theorem))));

    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula ell = F.Id("ell");
        Formula bound = F.Id("H");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Forall, Sp, ell, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, bound, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Hypothesis("hH", Seq(D(0), Sp, Le, Sp, bound),
                Hypothesis("ha", Seq(Norm(a), Sp, Le, Sp, bound),
                    Hypothesis("hb", Seq(Norm(b), Sp, Le, Sp, bound), Seq(
                        Norm(Seq(Pow(a, ell), Minus, Pow(b, ell))), Sp, Le, Sp,
                        CastReal(ell), Sp, Norm(Seq(a, Minus, b)), Sp,
                        Pow(bound, Seq(ell, Minus, D(1)))))))));
    }

    private static Formula CastReal(Formula value) =>
        Seq(Open, value, Colon, Sp, Mathbb, Grp(F.Id("R")), Close);
    private static Formula Hypothesis(string name, Formula proposition, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, proposition, Close, Sp, Rightarrow, Sp, body);
}
