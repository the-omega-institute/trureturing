using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CompletionPoints;

internal sealed class CompletionPointIntersectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/CompletionPoints/CompletionPointIntersection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired zero-defect completion equals intersection of component completion conditions.",
        H("Completion Point Intersection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-vanishing-is-componentwise-vanishing"),
                DeclarationHandle.Create(Prefix + "paired_zero_iff_component_zeros"),
                H("Paired vanishing is componentwise vanishing"),
                StatementSource.FromAuthor(PointStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix two defect readouts, their designated zero values, and a state.")),
                    Paragraph(Text(
                        "The paired defect equals the paired zero exactly when each component "
                            + "defect equals its corresponding zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-paired-zero-set-is-the-component-intersection"),
                DeclarationHandle.Create(Prefix + "paired_zero_set_eq_intersection"),
                H("The paired zero set is the component intersection"),
                StatementSource.FromAuthor(SetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Collect all states where the paired defect vanishes.")),
                    Paragraph(Text(
                        "By componentwise pair equality, this set is exactly the intersection of "
                            + "the first and second zero sets."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion, bool includeState)
    {
        Formula stateBinder = includeState
            ? Seq(F.Id("s"), Colon, Sp, F.Id("X"), Comma, Sp)
            : Seq();
        return Disp(Seq(
            Forall, Sp, F.Id("first"), Colon, Sp,
            Arrow(F.Id("X"), F.Id("A")), Comma, Sp,
            F.Id("second"), Colon, Sp, Arrow(F.Id("X"), F.Id("B")), Comma,
            RowBreak, Grp(),
            F.Id("a0"), Colon, Sp, F.Id("A"), Comma, Sp,
            F.Id("b0"), Colon, Sp, F.Id("B"), Comma, Sp,
            stateBinder, conclusion, Dot));
    }

    private static Formula PointStatement()
    {
        Formula paired = Call("ZeroAt",
            Seq(F.Id("x"), Sp, Mapsto, Sp,
                Call("pair", Call("first", F.Id("x")), Call("second", F.Id("x")))),
            Call("pair", F.Id("a0"), F.Id("b0")), F.Id("s"));
        Formula components = Seq(
            Call("ZeroAt", F.Id("first"), F.Id("a0"), F.Id("s")),
            Sp, Land, Sp,
            Call("ZeroAt", F.Id("second"), F.Id("b0"), F.Id("s")));
        return PrefixFormula(Seq(paired, Sp, Iff, Sp, Open, components, Close), true);
    }

    private static Formula SetStatement()
    {
        Formula paired = Call("zeroSet",
            Seq(F.Id("x"), Sp, Mapsto, Sp,
                Call("pair", Call("first", F.Id("x")), Call("second", F.Id("x")))),
            Call("pair", F.Id("a0"), F.Id("b0")));
        Formula intersection = Call("intersection",
            Call("zeroSet", F.Id("first"), F.Id("a0")),
            Call("zeroSet", F.Id("second"), F.Id("b0")));
        return PrefixFormula(Seq(paired, Sp, Eq, Sp, intersection), false);
    }
}
