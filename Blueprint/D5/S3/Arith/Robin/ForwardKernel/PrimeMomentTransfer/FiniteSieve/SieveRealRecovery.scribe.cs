using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveRealRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp interval sieve moments at real scales",
        H("Sharp interval sieve moments at real scales"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-sieve-intervals"),
                DeclarationHandle.Create(Prefix + "finite_sieve_intervals"),
                H("Real-scale recovery of the sharp interval moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume Montgomery–Soundararajan Theorem 1 (MSFinite) and Kuperberg "
                        + "Theorem 1.3 specialised to the smoothed interval weights (KuperbergSmoothed). "
                        + "Then the finite-sieve interval third moment and fourth Wick defect estimates "
                        + "FiniteSieveIntervals, the conclusion of Lemma 498.3(c), hold: "
                        + "for every fixed M at least one, the sharp cubic sieve moments divided "
                        + "by (H log H) to the power three halves, and the sharp fourth Wick "
                        + "defects divided by H squared times log H squared, tend to zero "
                        + "uniformly over all ordered interval endpoints in [0,M], as real H "
                        + "tends to infinity. The modulus is exactly the primorial through "
                        + "the natural floor of ((M+5)H) to the power ten.")),
                    Paragraph(Text(
                        "Set h to the natural floor of H and dilate every endpoint by H/h. "
                        + "The interval sums are unchanged, with the same modulus Q throughout. "
                        + "Eventually H is at most 2h and log H is at most 2 log h, so the "
                        + "integer estimates apply in the doubled window with doubled density "
                        + "constant. The scale (h log h) to the power k/2 is at most the "
                        + "corresponding real scale. Squarefreeness of the primorial and the "
                        + "existing density bound P(Q) at most B log H then give the result.")),
                    Paragraph(Text(
                        "KuperbergSmoothed is the specialization of Kuperberg Theorem 1.3 "
                        + "to the real smoothed interval weights used here, expressed as "
                        + "finite-sieve expectations. It is an explicit hypothesis. Fourier "
                        + "admissibility of the smoothed weights and the Ramanujan coordinate "
                        + "identity are not proved here.")),
                    Paragraph(Text(
                        "Together with MSSecond, interval_correlations_of_sieve_inputs gives "
                        + "IntervalCorrelations concreteSS."))),
                DescribeRole.Theorem))));
}
