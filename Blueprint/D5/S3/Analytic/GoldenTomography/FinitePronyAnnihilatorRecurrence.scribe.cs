using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyAnnihilatorRecurrenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Prony rational denominator determines a reciprocal monic "
            + "annihilator and an exact finite-order moment recurrence.",
        H("Finite Prony Annihilator Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-denominator-normalized-at-zero"),
                DeclarationHandle.Create(Prefix + "finite_prony_denominator_eval_zero"),
                H("The Prony denominator is normalized at zero"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nodes q_j, finitePronyDenominator is the polynomial product "
                            + "of 1 - q_j X. Its value at zero is one, matching the normalized "
                            + "denominator in formula (1295.3)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-annihilator-has-mode-count-degree"),
                DeclarationHandle.Create(Prefix + "finite_prony_annihilator_natDegree"),
                H("The reciprocal annihilator has the mode-count degree"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reciprocal characteristic polynomial is the product of X - q_j. "
                            + "Every factor is monic of degree one, so the product is monic "
                            + "and has degree equal to the indexed number of modes.")),
                    Paragraph(Text(
                        "This reciprocal orientation turns the source denominator coefficients "
                            + "into the forward-shift coefficients used by the exact moment "
                            + "recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-moment-annihilator-recurrence"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_moment_annihilator_recurrence"),
                H("The annihilator coefficients give the exact moment recurrence"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite moment c_n is a sum of weighted powers q_j^n. Expanding "
                            + "the recurrence residual mode by mode factors it into each "
                            + "weight, a time power, and the annihilator evaluated at q_j.")),
                    Paragraph(Text(
                        "Every q_j is a root of the reciprocal annihilator, so every shifted "
                            + "residual vanishes. This is formula (1295.4) in reciprocal "
                            + "characteristic coefficient order.")),
                    Paragraph(Text(
                        "The result is exact and finite-dimensional. Stability, repeated-node "
                            + "confluence, numerical coefficient recovery, and infinite Hankel "
                            + "limits remain outside this declaration."))),
                DescribeRole.Theorem)),
        []));
}
