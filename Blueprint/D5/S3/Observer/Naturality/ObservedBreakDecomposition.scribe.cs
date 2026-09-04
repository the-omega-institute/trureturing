using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class ObservedBreakDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Naturality/ObservedBreakDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observed symmetry breaking splits into observer and intrinsic defects.",
        H("Observed-Break Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observed-break-decomposition"),
                DeclarationHandle.Create(Prefix + "observed_break_decomposition"),
                H("Observed breaking has two exact sources"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observer term measures failure of the readout to intertwine the "
                            + "object update with the observed update. The second term reads the "
                            + "object's intrinsic update defect.")),
                    Paragraph(Text(
                        "The source writes the readout as an ordinary function, but the displayed "
                            + "identity requires preservation of subtraction. Lean records that "
                            + "repair by typing the readout as an AddMonoidHom.")),
                    Paragraph(Text(
                        "After applying map_sub, additive cancellation gives the exact split. "
                            + "This declaration is the bind-only companion of the explicit "
                            + "nonadditive counterexample below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonadditive-observer-break-counterexample"),
                DeclarationHandle.Create(
                    Prefix + "nonadditive_observer_break_counterexample"),
                H("Additivity cannot be dropped"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the integers, the quadratic readout O(z)=z z, the successor object "
                            + "update, and the identity observed update violate the decomposition "
                            + "at z=1.")),
                    Paragraph(Text(
                        "This concrete computation is the module's escape witness: it establishes "
                            + "that the repaired additivity hypothesis is mathematically necessary, "
                            + "rather than a Lean convenience."))),
                DescribeRole.Theorem))));

    private static Formula DecompositionFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula jx = new Formula.Subscript(F.Id("J"), F.Id("X"));
        Formula jy = new Formula.Subscript(F.Id("J"), F.Id("Y"));
        Formula observer = F.Id("O");
        Formula x = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula observedValue = Apply(observer, x);
        Formula updatedObserved = Apply(jy, observedValue);
        Formula updatedObject = Apply(jx, x);
        Formula observerDefect = Difference(
            updatedObserved, Apply(observer, updatedObject));
        Formula intrinsicDefect = Apply(
            observer, Difference(updatedObject, x));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(xType, type), Comma, Sp, Typed(yType, type), Comma),
            Seq(Grp(), Typeclass("AddGroup", xType), Comma, Sp,
                Typeclass("AddGroup", yType), Comma),
            Seq(Grp(), Typed(jx, Arrow(xType, xType)), Comma, Sp,
                Typed(jy, Arrow(yType, yType)), Comma),
            Seq(Grp(), Typed(observer, Call("AddMonoidHom", xType, yType)), Comma, Sp,
                Typed(x, xType), Comma),
            Seq(Grp(), Difference(updatedObserved, observedValue), Sp, Eq, Sp,
                observerDefect, Sp, Plus, Sp, intrinsicDefect, Dot),
        ]));
    }

    private static Formula CounterexampleFormula()
    {
        Formula z = F.Id("z");
        Formula one = D(1);
        Formula observerAtOne = Apply(F.Id("O"), one);
        Formula jxAtOne = Apply(new Formula.Subscript(F.Id("J"), F.Id("X")), one);
        Formula jyAtObserver = Apply(
            new Formula.Subscript(F.Id("J"), F.Id("Y")), observerAtOne);

        return Disp(new Formula.Aligned([
            Seq(F.Id("O"), Open, z, Close, Sp, Eq, Sp, z, Sp, Cdot, Sp, z,
                Comma, Sp,
                new Formula.Subscript(F.Id("J"), F.Id("X")), Open, z, Close,
                Sp, Eq, Sp, z, Plus, one, Comma),
            Seq(Grp(), new Formula.Subscript(F.Id("J"), F.Id("Y")), Open, z, Close,
                Sp, Eq, Sp, z, Comma),
            Seq(Grp(), Difference(jyAtObserver, observerAtOne), Sp, Neq, Sp,
                Difference(jyAtObserver, Apply(F.Id("O"), jxAtOne)),
                Sp, Plus, Sp,
                Apply(F.Id("O"), Difference(jxAtOne, one)), Dot),
        ]));
    }

    private static Formula Difference(Formula left, Formula right) =>
        Seq(Open, left, Sp, Minus, Sp, right, Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
