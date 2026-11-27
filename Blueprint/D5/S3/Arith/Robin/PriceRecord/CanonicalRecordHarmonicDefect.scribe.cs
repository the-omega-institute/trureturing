using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CanonicalRecordHarmonicDefectDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted harmonic sum bounds the complete defect of the canonical strict record "
        + "and gives little-o decay relative to log X/X².",
        H("Canonical record harmonic defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-record-higher-loss-bound"),
                DeclarationHandle.Create(Gid + ".canonical_record_higher_loss_bound"),
                H("Harmonic bound for the combined higher loss"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be real with X ≥ max(exp(4), 729). Set q = referencePrice(X) = 1/(X log X), "
                        + "μ = firstLayerPrice(X + 1) = log(1 + 1/(X + 1))/log(X + 1), "
                        + "and m = strictInteger(μ). Write B = 6 log 2 + 1 + log(6 log X). "
                        + "The sum completeSecondLayerLoss(X, m) + completeHigherLayerLoss(X, m) "
                        + "lies between 0 and 3B/X², inclusive.")),
                    Paragraph(Text(
                        "The relative price bracket uses the prices (1 ± 3/X)q. "
                        + "Every active layer j ≥ 2 has a half-open cutoff interval of width at most "
                        + "27/√X ≤ 1, so at most one prime crosses in that layer. The lower-price cutoff "
                        + "is at most 2X^(1/j) and active layers have j < 6 log X. "
                        + "Charge the crossing log p ≤ log 2 + log X/j and sum these weights up to "
                        + "the integer part of 6 log X. The harmonic-number estimate gives total mass "
                        + "at most (log X)B. The inventory at q is contained in the inventory at μ. "
                        + "Each additional coordinate costs at most (q − μ) log p and "
                        + "q − μ ≤ 3q/X. Multiplying by the mass bound gives 3B/X²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-record-harmonic-defect"),
                DeclarationHandle.Create(Gid + ".canonical_record_harmonic_defect"),
                H("Harmonic bound for the complete defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real X ≥ max(exp(4), 729), set m = strictInteger(firstLayerPrice(X + 1)), "
                        + "D = actualDefect(X, m) and R = D − completeFirstLayerLoss(X, m). "
                        + "With B = 6 log 2 + 1 + log(6 log X), the residual satisfies 0 ≤ R ≤ 3B/X² "
                        + "and the complete defect satisfies 0 ≤ D ≤ (3B + 7/4)/X². "
                        + "The decomposition of D identifies R with the combined loss from layers two and "
                        + "higher. The canonical record power bound gives completeFirstLayerLoss(X, m) "
                        + "≤ (7/4)/X² for the same strict optimizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-record-higher-loss-is-little-o"),
                DeclarationHandle.Create(Gid + ".canonical_record_higher_loss_isLittleO"),
                H("Little-o decay of the combined higher loss"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real X tending to positive infinity and m = strictInteger(firstLayerPrice(X + 1)), "
                        + "completeSecondLayerLoss(X, m) + completeHigherLayerLoss(X, m) is little-o "
                        + "of log X/X². Dividing the harmonic bound by log X/X² gives a sum of "
                        + "a constant divided by log X and 3 log(log X)/log X, which both tend to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-record-defect-is-little-o"),
                DeclarationHandle.Create(Gid + ".canonical_record_defect_isLittleO"),
                H("Little-o decay of the complete defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "As real X tends to positive infinity, actualDefect(X, "
                        + "strictInteger(firstLayerPrice(X + 1))) is little-o of log X/X². "
                        + "The first-layer allowance contributes at most 7/(4 log X) to the "
                        + "normalized bound and therefore tends to zero as well."))),
                DescribeRole.Theorem))));
}
