using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PostprocessingKernelMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/PostprocessingKernelMonotonicity."
            + "postprocessing_kernel_mono";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Postprocessing can only enlarge a readout equality kernel.",
        H("Postprocessing Kernel Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("postprocessing-can-only-enlarge-the-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Postprocessing can only enlarge the kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Two source states in the original equality kernel have identical "
                        + "readout values.")),
                Paragraph(Text(
                    "Applying any deterministic postprocessing map to that equality keeps "
                        + "the outputs equal. The original kernel is therefore contained in "
                        + "the postprocessed kernel.")),
                Paragraph(Text(
                    "A Boolean identity readout followed by constant postprocessing witnesses "
                        + "that the inclusion can be strict. No computational power placed "
                        + "after the same readout can recover the collapsed distinction."))),
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
        Formula sourceKernel = Call("K", readout);
        Formula postprocessed = Seq(postprocess, Circ, readout);
        Formula targetKernel = Call("K", postprocessed);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, visible, Comma, Sp, result),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Seq(source, Sp, To, Sp, visible)),
            Comma, RowBreak, Grp(),
            Typed(postprocess, Seq(visible, Sp, To, Sp, result)),
            Comma, RowBreak, Grp(),
            sourceKernel, Sp, Subseteq, Sp, targetKernel, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
