using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class MeasurablePostprocessingDefectContractionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction."
            + "measurable_postprocessing_defect_le";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measurable target postprocessing contracts the source-fiber defect of observable kernel laws.",
        H("Measurable Postprocessing Defect Contraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("measurable-postprocessing-defect-contraction"),
            DeclarationHandle.Create(Declaration),
            H("Measurable postprocessing contracts the observable-kernel defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The event-supremum total-variation distance is constructed directly from "
                        + "measures. Each observable law is the corresponding row of K mapped "
                        + "through q, and the postprocessed law maps that measure through r.")),
                Paragraph(Text(
                    "For every measurable event in C, measurability of r identifies its "
                        + "probability after mapping with the probability of the measurable "
                        + "preimage event in B. The associated directed gap is therefore one of "
                        + "the terms in the original event supremum.")),
                Paragraph(Text(
                    "The pointwise contraction is applied to every pair of source states with "
                        + "the same q-value and then lifted through the outer supremum. The proof "
                        + "uses pinned Mathlib's kernel and measure map computation rules."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula source = F.Id("X");
        Formula target = F.Id("B");
        Formula output = F.Id("C");
        Formula kernel = F.Id("K");
        Formula readout = F.Id("q");
        Formula postprocess = F.Id("r");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, target, Comma, Sp, output), type),
            Comma, RowBreak, Grp(),
            Call("MeasurableSpace", source), Comma, Sp,
            Call("MeasurableSpace", target), Comma, Sp,
            Call("MeasurableSpace", output), Comma, RowBreak, Grp(),
            Typed(kernel, Call("Kernel", source, source)), Comma, Sp,
            Typed(readout, Arrow(source, target)), Comma, RowBreak, Grp(),
            Typed(postprocess, Arrow(target, output)), Comma, Sp,
            Call("Measurable", postprocess), Sp, Rightarrow, RowBreak, Grp(),
            Call("postprocessedObservableKernelDefect", kernel, readout, postprocess),
            Sp, Leq, Sp,
            Call("observableKernelDefect", kernel, readout), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
