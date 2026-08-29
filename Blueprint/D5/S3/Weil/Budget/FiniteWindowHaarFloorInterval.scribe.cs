using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class FiniteWindowHaarFloorIntervalDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An operator-norm certificate for windowed Toeplitz moments gives a rigorous "
            + "two-sided interval for the finite Haar floor.",
        H("Finite-Window Haar-Floor Interval"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-window-haar-floor-interval"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/FiniteWindowHaarFloorInterval."
                        + "finite_window_haar_floor_interval"),
                H("Windowed Toeplitz data bounds the exact Haar floor"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two integer-indexed moment functions construct the true and "
                            + "windowed Toeplitz matrices entry by entry. Their displayed "
                            + "conjugate symmetries make both matrices Hermitian.")),
                    Paragraph(Text(
                        "The error radius is exactly twice the finite sum of the supplied "
                            + "tail bounds. If it dominates the matrix operator-norm error, "
                            + "the true smallest eigenvalue lies within that radius of the "
                            + "windowed smallest eigenvalue.")),
                    Paragraph(Text(
                        "The Lean proof identifies each smallest Hermitian eigenvalue with "
                            + "the infimum of its Rayleigh quotient and applies the operator "
                            + "norm bound in both directions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula depth = F.Id("N");
        Formula moment = F.Id("c");
        Formula windowMoment = F.Id("chat");
        Formula tail = F.Id("tau");
        Formula index = F.Id("r");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula trueMatrix = F.Id("T");
        Formula windowMatrix = F.Id("That");
        Formula radius = F.Id("Delta");
        Formula momentType = Seq(integer, Sp, To, Sp, complex);
        Formula tailType = Seq(nat, Sp, To, Sp, real);
        Formula momentAt = Apply(moment, Seq(row, Minus, column));
        Formula windowMomentAt = Apply(windowMoment, Seq(row, Minus, column));
        Formula matrixDomain = Seq(
            row, Comma, column, InMacro, Call("Fin", Seq(depth, Plus, D(1))));
        Formula trueDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, trueMatrix, Sp, Eq, Sp,
            Call("Matrix", Lambda(matrixDomain, momentAt)));
        Formula windowDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, windowMatrix, Sp, Eq, Sp,
            Call("Matrix", Lambda(matrixDomain, windowMomentAt)));
        Formula radiusDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, radius, Sp, Eq, Sp,
            D(2), Sp, Cdot, Sp, Sum, Underscore,
            Grp(column, Eq, D(1)), Caret, Grp(depth), Sp, Apply(tail, column));
        Formula momentSymmetry = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("r"), integer)],
            Seq(Overline, Grp(Apply(moment, index)), Sp, Eq, Sp,
                Apply(moment, Seq(Minus, index))));
        Formula windowSymmetry = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("r"), integer)],
            Seq(Overline, Grp(Apply(windowMoment, index)), Sp, Eq, Sp,
                Apply(windowMoment, Seq(Minus, index))));
        Formula normPremise = Seq(
            Call("opNorm", Seq(trueMatrix, Minus, windowMatrix)), Sp, Leq, Sp, radius);
        Formula trueFloor = Call("lambdaMin", trueMatrix);
        Formula windowFloor = Call("lambdaMin", windowMatrix);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, depth, Colon, Sp, nat, Comma, Sp,
                moment, Comma, windowMoment, Colon, Sp, momentType, Comma, Sp,
                tail, Colon, Sp, tailType, Comma),
            Seq(momentSymmetry, Sp, Land, Sp, windowSymmetry, Comma),
            Seq(trueDefinition, Comma, Sp, windowDefinition, Comma),
            Seq(radiusDefinition, Comma, Sp, normPremise, Sp, Rightarrow),
            Seq(windowFloor, Sp, Minus, Sp, radius, Sp, Leq, Sp, trueFloor,
                Sp, Land, Sp, trueFloor, Sp, Leq, Sp, windowFloor, Sp, Plus, Sp,
                radius, Dot),
        ]));
    }
}
