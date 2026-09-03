using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class PrimitiveIntegralSelectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/PrimitiveIntegralSelection."
            + "primitive_integral_selection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace and signed determinant classify a nonnegative integral binary matrix "
            + "up to simultaneous coordinate swap.",
        H("Primitive Integral Selection"),
        Blocks(Describe.Lean(
            DescribeId.Create("primitive-integral-selection"),
            DeclarationHandle.Create(Declaration),
            H("Trace one and determinant minus one select the Fibonacci matrix"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The trace condition leaves the two possible diagonal orders. "
                        + "In either order, the signed determinant condition forces the "
                        + "product of the off-diagonal natural entries to equal one.")),
                Paragraph(Text(
                    "Both off-diagonal entries are therefore one. The two displayed "
                        + "matrices differ by simultaneously swapping the coordinates."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula finTwo = Call("Fin", D(2));
        Formula matrixType = Call("Matrix", finTwo, finTwo, natural);
        Formula matrix = F.Id("M");
        Formula integerMatrix = Call("cast", integer, matrix);
        Formula fibonacci = Call("matrix2", D(1), D(1), D(1), D(0));
        Formula swapped = Call("matrix2", D(0), D(1), D(1), D(1));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(matrix, matrixType), Comma),
            Seq(
                Grp(), Open, Call("trace", matrix), Sp, Eq, Sp, D(1), Sp,
                Land, Sp, Call("det", integerMatrix), Sp, Eq, Sp, Minus, D(1),
                Close, Sp, Rightarrow),
            Seq(
                Grp(), Open, matrix, Sp, Eq, Sp, fibonacci, Sp, Lor, Sp,
                matrix, Sp, Eq, Sp, swapped, Close, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

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
