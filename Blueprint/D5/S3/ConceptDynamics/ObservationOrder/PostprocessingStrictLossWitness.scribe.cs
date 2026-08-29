using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PostprocessingStrictLossWitnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/PostprocessingStrictLossWitness."
            + "collapsed_distinction_witnesses_strict_loss";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A collapsed distinction witnesses strict information loss under postprocessing.",
        H("Postprocessing Strict-Loss Witness"),
        Blocks(Describe.Lean(
            DescribeId.Create("postprocessing-strict-loss-witness"),
            DeclarationHandle.Create(Declaration),
            H("Postprocessing Strict-Loss Witness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A strict-loss witness is separated by the original readout and identified after postprocessing.")),
                Paragraph(Text(
                    "The witness lies in the processed kernel outside the raw kernel and refutes global injectivity of the postprocessor."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("raw_separation_and_processed_collision"), Sp, Rightarrow, Sp,
            F.Id("strict_information_loss"), Dot));
}
