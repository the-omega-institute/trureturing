using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.GoldenSpectrum;

internal sealed class GoldenCriticalSupportCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalSupportCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-line support is equivalent to unit support in the golden coordinate.",
        H("Golden Critical Support Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-support-iff-golden-unitary-support"),
                DeclarationHandle.Create(
                    Prefix + "critical_support_iff_golden_unitary_support"),
                H("Critical support equals golden unitary support"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem lifts the pointwise unit-circle criterion to an arbitrary "
                            + "set of spectral points.")),
                    Paragraph(Text(
                        "It can be instantiated with a zero set after that zero carrier has been "
                            + "supplied. The theorem itself is independent of zeta.")),
                    Paragraph(Text(
                        "A separate finite counterexample shows that reciprocal pair balance is "
                            + "strictly weaker than pointwise critical support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-reflection-orbit-not-critical"),
                DeclarationHandle.Create(
                    Prefix + "balanced_reflection_orbit_need_not_be_critical"),
                H("Pair balance need not imply criticality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A reflected two-point orbit away from the critical line has reciprocal "
                            + "charges whose products are one.")),
                    Paragraph(Text(
                        "The orbit therefore satisfies global pair balance while failing the "
                            + "pointwise fixed-line condition."))),
                DescribeRole.Theorem))));
}
