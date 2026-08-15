using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class ContractionSupremumOrderDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula metric) => Seq(
        F.Id("eta"), Underscore, Grp(metric), Open, Gamma, Comma, F.Id("u"), Close);

    private static Formula AxisSup(Formula metric) => Seq(
        Operatorname, Grp(F.Id("sup")), Underscore,
        Grp(D(0), Sp, Lt, Sp, F.Id("u"), Sp, Lt, Sp, D(1)), Sp, Ratio(metric));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pointwise SLD-KM-RLD amplitude-damping order lifts to the corresponding "
        + "positive open-axis suprema of the scalar contraction-ratio model.",
        H("Amplitude-Damping Contraction Suprema Are Ordered"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-positive-axis-contraction-ratio-suprema-are-ordered"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/ContractionSupremumOrder.contraction_supremum_order"),
                H("The positive-axis contraction-ratio suprema are ordered"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Le, Gamma, Sp, Lt, Sp, D(1), Sp, Rightarrow, Sp,
                    AxisSup(F.Id("SLD")), Sp, Le, Sp, AxisSup(F.Id("KM")), Sp, Le, Sp,
                    AxisSup(F.Id("RLD"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a damping parameter gamma in the interval from zero inclusive to one "
                        + "exclusive. Taking the supremum over the positive open Bloch axis preserves "
                        + "the imported pointwise ordering of the SLD, KM, and RLD coherence ratios. "
                        + "Boundedness follows from the imported RLD endpoint bound, while the two "
                        + "supremum comparisons use monotonicity of the indexed supremum.")),
                    Paragraph(Text(
                        "This theorem closes the sup-level omission recorded by the producer at "
                        + "ContractionSpectrumOrder.lean:139-142: it lifts the scalar positive-axis "
                        + "pointwise order to the corresponding iSup order. It does NOT close the "
                        + "producer's recorded contraction-coefficient gap. The all-state reduction "
                        + "remains open and is NOT discharged by this wave: there is no all-state "
                        + "coefficient definition or reduction from all input states to the positive "
                        + "scalar axis. No claim is made about the negative axis."))),
                DescribeRole.Theorem))));
}
