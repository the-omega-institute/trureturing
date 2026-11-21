using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoForwardGeodesicCommonSequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");
    private static readonly LibraryNoteRef Masking =
        LibraryNoteRef.Create("D5/L/Divergence/ambainis2000private");
    private static readonly LibraryNoteRef ConditionalEntropy =
        LibraryNoteRef.Create("D5/L/Divergence/bluhm2023continuity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One sequence of faithful three-qubit pairs gives a log 2 gap in both forward deficits for every fixed positive geodesic parameter.",
        H("A common sequence for both forward deficits"),
        Blocks(
            Paragraph(Text("Theorem 10.16 already rules out a trace-distance modulus at fixed B by relabeling the balanced classical label as C and adjoining an independent faithful B using Proposition 4.3. In that reduction the AC marginal carries the varying signal and label. The construction here keeps AC and BC fixed and matches AB within each pair.")),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-common-sequence-eventually-uniform-regularization"),
                DeclarationHandle.Create(Prefix + "eventually_uniform_regularization"),
                H("Regularization on compact parameter sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For fixed 0 < u < 1/2, joint continuity of the spectral quadratic form in t and the regularization parameter gives a single right neighborhood of zero for each compact subset of 0 < t < 1 and each positive error tolerance. The spectrum of the first matrix stays on a compact real interval, so both positive matrix powers have the continuous functional calculus needed at the singular boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-common-sequence-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("One sequence for every fixed 0 < t ≤ 1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Masking, ConditionalEntropy),
                Blocks(Paragraph(Text(
                    "There is one sequence of faithful three-qubit pairs. Within each pair the AB, AC and BC marginals agree. For both states at every index B is I/2 and AC and BC are I/4. The shared AB marginal varies with the index. The trace distance tends to zero from above. For every fixed 0 < t ≤ 1 both signed forward gaps converge to log 2, with one-sided reference I/2 and the actual C marginal in the two-sided deficit. The proof uses u_n = 1/(n+3), controls the error within u_n on [u_n, 1−u_n], and also enforces the error bound at t = 1. Every fixed interior t eventually lies in these intervals."))),
                DescribeRole.Theorem)),
        []));
}
