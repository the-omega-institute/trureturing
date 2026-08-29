using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class ConstantPostprocessingStrictLossDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/ConstantPostprocessingStrictLoss."
            + "constant_postprocessing_strictly_enlarges_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant postprocessing strictly loses every witnessed distinction.",
        H("Constant Postprocessing Strict Loss"),
        Blocks(Describe.Lean(
            DescribeId.Create("constant-postprocessing-strictly-loses-a-distinction"),
            DeclarationHandle.Create(Declaration),
            H("Constant postprocessing strictly loses a witnessed distinction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The original readout is assumed to distinguish one supplied pair of "
                        + "source states.")),
                Paragraph(Text(
                    "Monotonicity gives inclusion of the original kernel in the constant "
                        + "postprocessed kernel. The supplied pair is absent from the first "
                        + "kernel and present in the second, proving strictness.")),
                Paragraph(Text(
                    "The conclusion applies to every inhabited target chosen for the constant "
                        + "output and requires no further structure."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula visible = F.Id("Y");
        Formula result = F.Id("Z");
        Formula readout = F.Id("q");
        Formula collapsed = F.Id("c");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula constantProcessed = Call("constantAfter", collapsed, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, visible, Comma, Sp, result),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Seq(source, Sp, To, Sp, visible)), Comma, Sp,
            Typed(collapsed, result), Comma, RowBreak, Grp(),
            Typed(Seq(left, Comma, Sp, right), source), Comma, RowBreak, Grp(),
            Call("SeparatedBy", readout, left, right), Sp, Rightarrow, RowBreak, Grp(),
            Call("StrictSubset", Call("K", readout),
                Call("K", constantProcessed)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
