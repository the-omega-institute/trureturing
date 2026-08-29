using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class RecoverablePostprocessingKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/RecoverablePostprocessingKernelEquality."
            + "recoverable_postprocessing_preserves_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recoverable postprocessing preserves the readout kernel exactly.",
        H("Recoverable Postprocessing Kernel Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("recoverable-postprocessing-preserves-the-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Recoverable postprocessing preserves the kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A recovery map is required to undo postprocessing only on values that "
                        + "actually occur in the readout image.")),
                Paragraph(Text(
                    "Processed equality is reflected through recovery to original equality. "
                        + "Original equality is preserved forward by postprocessing, giving "
                        + "the two kernel inclusions and hence equality.")),
                Paragraph(Text(
                    "This image-relative recovery condition is weaker than global injectivity "
                        + "of the postprocessing map."))),
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
        Formula postprocess = F.Id("g");
        Formula recover = F.Id("h");
        Formula processed = Seq(postprocess, Circ, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, visible, Comma, Sp, result),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Seq(source, Sp, To, Sp, visible)), Comma, Sp,
            Typed(postprocess, Seq(visible, Sp, To, Sp, result)), Comma, Sp,
            Typed(recover, Seq(result, Sp, To, Sp, visible)),
            Comma, RowBreak, Grp(),
            Call("RecoversOnImage", recover, postprocess, readout),
            Sp, Rightarrow, RowBreak, Grp(),
            Call("K", processed), Sp, Eq, Sp, Call("K", readout), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
