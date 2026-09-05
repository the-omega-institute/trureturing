using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SchurShiftedTemplateLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/SchurShiftedTemplateLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Schur templates give the classical threefold lift and the width-10 "
            + "shifted-template lift.",
        H("Schur Shifted-Template Lifts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-coloring-small-values"),
                DeclarationHandle.Create(Module + "schurColoringSmallValues"),
                H("Small Schur colorings and the first obstruction"),
                StatementSource.FromAuthor(SmallValuesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first clause constructs the singleton one-coloring. The second "
                        + "uses the explicit two-color assignment with color classes {1,4} "
                        + "and {2,3}. The final clause rules out a one-coloring of {1,2} "
                        + "using the monochromatic equation 1+1=2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classical-schur-threefold-lift"),
                DeclarationHandle.Create(Module + "classicalLift"),
                H("The classical Schur threefold lift"),
                StatementSource.FromAuthor(ClassicalLiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary natural k and n, two translated copies of the input "
                        + "coloring surround the interval from n+1 through 2n+1, which is "
                        + "assigned one new color. The construction yields length 3n+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-template-compatibility-certificates"),
                DeclarationHandle.Create(Module + "shiftedTemplateCompatibilityCertificates"),
                H("Finite compatibility and width-10 carry certificates"),
                StatementSource.FromAuthor(CompatibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five conjuncts state the ordinary-label compatibility check, the "
                        + "shifted old-label carry check, the two separate tail checks for A "
                        + "and B, and the quotient-remainder addition law for positive block "
                        + "coordinates. The labels are the literal Table-II rows F and M=L, "
                        + "with the two-cell tail Q=(A,B)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("width-ten-shifted-template-lift"),
                DeclarationHandle.Create(Module + "shiftedTemplateLift"),
                H("The width-10 shifted-template lift"),
                StatementSource.FromAuthor(ShiftedLiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary natural k and n, the literal width-10 shifted template "
                        + "and its two-cell tail transform any k-color Schur coloring of "
                        + "length n into a (k+2)-color Schur coloring of length 10n+2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-lift-numerical-consequences"),
                DeclarationHandle.Create(Module + "schurLiftNumericalConsequences"),
                H("Numerical consequences of the two lifts"),
                StatementSource.FromAuthor(NumericalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the classical lift to the explicit two-coloring gives a "
                        + "three-coloring of length 13. Applying the width-10 lift to the "
                        + "same base coloring gives a four-coloring of length 42."))),
                DescribeRole.Theorem))));

    private static Formula SmallValuesFormula() => Disp(Seq(
        Schur(D(1), D(1)), Sp, Land, Sp,
        Schur(D(2), D(4)), Sp, Land, Sp,
        Neg, Sp, Paren(Schur(D(1), D(2)))));

    private static Formula ClassicalLiftFormula() => Disp(Seq(
        Forall, Sp, F.Id("k"), Comma, Sp, F.Id("n"), InMacro, Sp,
        Naturals(), Comma, Sp,
        Schur(F.Id("k"), F.Id("n")), Sp, Rightarrow, Sp,
        Schur(Seq(F.Id("k"), Plus, D(1)),
            Seq(D(3), F.Id("n"), Plus, D(1)))));

    private static Formula ShiftedLiftFormula() => Disp(Seq(
        Forall, Sp, F.Id("k"), Comma, Sp, F.Id("n"), InMacro, Sp,
        Naturals(), Comma, Sp,
        Schur(F.Id("k"), F.Id("n")), Sp, Rightarrow, Sp,
        Schur(Seq(F.Id("k"), Plus, D(2)),
            Seq(D(1, 0), F.Id("n"), Plus, D(2)))));

    private static Formula NumericalFormula() => Disp(Seq(
        Schur(D(3), D(1, 3)), Sp, Land, Sp, Schur(D(4), D(4, 2))));

    private static Formula CompatibilityFormula()
    {
        Formula fx = Sub(F.Id("f"), F.Id("x"));
        Formula fy = Sub(F.Id("f"), F.Id("y"));
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula a = F.Id("a");
        Formula resultLabel = Label(Call("shiftedTemplateResultFirst", fx, fy, u, v),
            Call("shiftedTemplateOutCol", u, v));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, fx, Comma, Sp, fy, Colon, Sp, F.Id("Bool"), Comma, Sp,
                u, Comma, Sp, v, Colon, Sp, Call("Fin", D(1, 0)), Comma, Sp,
                a, Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                Neg, Sp, Paren(Seq(
                    NewLabel(Label(fx, u)), Sp, Eq, Sp, Call("some", a), Sp, Land, Sp,
                    NewLabel(Label(fy, v)), Sp, Eq, Sp, Call("some", a), Sp, Land, Sp,
                    NewLabel(resultLabel), Sp, Eq, Sp, Call("some", a))), Sp, Land),
            Seq(
                Forall, Sp, fx, Comma, Sp, fy, Colon, Sp, F.Id("Bool"), Comma, Sp,
                u, Comma, Sp, v, Colon, Sp, Call("Fin", D(1, 0)), Comma, Sp,
                Call("shiftedTemplateOldCompatible", fx, fy, u, v),
                Sp, Eq, Sp, F.Id("true"), Sp, Land),
            Seq(
                Forall, Sp, fx, Comma, Sp, fy, Colon, Sp, F.Id("Bool"), Comma, Sp,
                u, Comma, Sp, v, Colon, Sp, Call("Fin", D(1, 0)), Comma, Sp,
                Call("val", u), Plus, Call("val", v), Sp, Eq, Sp, D(9),
                Sp, Rightarrow, Sp,
                Neg, Sp, Paren(Seq(
                    NewLabel(Label(fx, u)), Sp, Eq, Sp, Call("some", D(0)), Sp, Land, Sp,
                    NewLabel(Label(fy, v)), Sp, Eq, Sp, Call("some", D(0)))), Sp, Land),
            Seq(
                Forall, Sp, fx, Comma, Sp, fy, Colon, Sp, F.Id("Bool"), Comma, Sp,
                u, Comma, Sp, v, Colon, Sp, Call("Fin", D(1, 0)), Comma, Sp,
                Paren(Seq(
                    Call("val", u), Plus, Call("val", v), Sp, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    Neg, Sp, Paren(Seq(
                        fx, Sp, Eq, Sp, F.Id("true"), Sp, Land, Sp,
                        fy, Sp, Eq, Sp, F.Id("true"))))), Sp, Rightarrow, Sp,
                Paren(Seq(
                    Call("val", u), Plus, Call("val", v), Sp, Eq, Sp, D(0),
                    Sp, Lor, Sp,
                    Call("val", u), Plus, Call("val", v), Sp, Eq, Sp, D(1, 0))),
                Sp, Rightarrow, Sp,
                Neg, Sp, Paren(Seq(
                    NewLabel(Label(fx, u)), Sp, Eq, Sp, Call("some", D(1)), Sp, Land, Sp,
                    NewLabel(Label(fy, v)), Sp, Eq, Sp, Call("some", D(1)))), Sp, Land),
            Seq(
                Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                F.Id("z"), InMacro, Sp, Naturals(), Comma, Sp,
                D(1), Sp, Leq, Sp, F.Id("x"), Sp, Land, Sp,
                D(1), Sp, Leq, Sp, F.Id("y"), Sp, Land, Sp,
                F.Id("x"), Plus, F.Id("y"), Sp, Eq, Sp, F.Id("z"), Sp,
                Rightarrow, Sp, Paren(Seq(
                    Call("blockRow", F.Id("z")), Sp, Eq, Sp,
                    Call("blockRow", F.Id("x")), Plus,
                    Call("blockRow", F.Id("y")), Plus,
                    Call("shiftedTemplateCarry",
                        Call("blockCol", F.Id("x")), Call("blockCol", F.Id("y"))),
                    Sp, Land, Sp,
                    Call("blockCol", F.Id("z")), Sp, Eq, Sp,
                    Call("shiftedTemplateOutCol",
                        Call("blockCol", F.Id("x")), Call("blockCol", F.Id("y"))))), Dot),
        ]));
    }

    private static Formula Schur(Formula colors, Formula length) =>
        Call("HasSchurColoring", colors, length);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Label(Formula first, Formula column) =>
        Call("shiftedTemplateLabel", first, column);

    private static Formula NewLabel(Formula label) =>
        Call("shiftedTemplateNewLabel", label);

    private static Formula Sub(Formula value, Formula subscript) =>
        new Formula.Subscript(value, subscript);

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { F.Id(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
