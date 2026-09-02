using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenRationalCirclePhaseInjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden quotient-circle phase remains faithful on positive rational scales.",
        H("Golden Rational Circle-Phase Injectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-rational-golden-circle-point-injective"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenPrimeCircle/GoldenRationalCirclePhaseInjectivity.positive_rational_golden_circle_point_injective"),
                H("Positive rational scales have distinct golden circle points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Although one whole golden shell is invisible on the quotient circle, two positive rational scales can share a golden circle point only when they are equal.")),
                    Paragraph(Text(
                        "The proof reuses the canonical golden scale circle, its additive-circle quotient, and the existing rational shell-rigidity theorem. It supplies exact injectivity without a quantitative separation bound."))),
                DescribeRole.Theorem))));
}
