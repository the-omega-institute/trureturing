using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ShiftFiberPoincareInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compactly supported Weil test has the sharp finite-Dirichlet spectral gap along "
            + "every positive real translation.",
        H("Shift-Fiber Poincare Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shift-fiber-poincare-inequality"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/ShiftFiberPoincareInequality."
                        + "shift_fiber_poincare_inequality"),
                H("The support-controlled translation gap"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the canonical even smooth compactly supported complex "
                            + "Weil-test space. The displayed support premise uses the ordinary "
                            + "function support on the exact real interval from minus L to L.")),
                    Paragraph(Text(
                        "The public count is floor(2L/a)+1. The public gap is four times the "
                            + "square of sin(pi/(2(count+1))), and translationEnergy uses the "
                            + "source shift f(x-a).")),
                    Paragraph(Text(
                        "The proof applies the frozen sharp real path-averaging bound to the real "
                            + "and imaginary parts, obtains the complex Dirichlet path estimate, "
                            + "and integrates its fibers over one fundamental interval."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula shift = F.Id("a");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula supportInterval = Seq(
            OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket);
        Formula positiveShift = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThan, shift);
        Formula supportPremise = Seq(
            Call("support", test), Sp, Subseteq, Sp, supportInterval);
        Formula premises = new Formula.Logic(
            positiveShift, FormulaLogicOperator.And, supportPremise);
        Formula conclusion = new Formula.Relation(
            new Formula.Binary(
                Call("shiftFiberGap", scale, shift),
                FormulaBinaryOperator.Multiply,
                Call("l2Mass", test)),
            FormulaRelationOperator.LessThanOrEqual,
            Call("translationEnergy", test, shift));

        return Disp(Seq(
            Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            scale, Comma, Sp, shift, InMacro, Sp, reals, Comma, Sp,
            premises, Sp, Rightarrow, Sp, conclusion));
    }
}
