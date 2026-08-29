using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class InjectivePostprocessingKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/InjectivePostprocessingKernelEquality."
            + "injective_postprocessing_preserves_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective postprocessing preserves an observation kernel exactly.",
        H("Injective Postprocessing"),
        Blocks(Describe.Lean(
            DescribeId.Create("injective-postprocessing-kernel-equality"),
            DeclarationHandle.Create(Declaration),
            H("Injective Postprocessing"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Postprocessing maps raw readouts into a new output representation.")),
                Paragraph(Text(
                    "Injectivity prevents distinct raw outputs from collapsing, so the induced observation kernel is unchanged."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("injective_postprocessing"), Sp, Rightarrow, Sp,
            F.Id("equal_observation_kernels"), Dot));
}
