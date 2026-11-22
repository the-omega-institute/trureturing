using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CoordinatePinchingLossDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/Auric/CoordinatePinchingLoss.";

    private static LibraryNoteRef EldarForney =>
        LibraryNoteRef.Create("D5/L/Entropy/eldarforney2001quantumdetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp attainable AURIC decoding loss at fixed block probabilities and a Walsh counterexample.",
        H("The decoding loss within a fixed coarse record law"),
        Blocks(
            Paragraph(Text("Use a nonempty finite carrier of size N, uniform phase labels, flat column-orthogonal phases and nonnegative normalized amplitudes. Keep the root coordinate partition c fixed, with r_b coordinates in block b and prescribed probabilities q_b. The coherent decoder uses an arbitrary label POVM. The recorded decoder optimizes over every admissible same-register continuation after the identity-unitary root PVM and every joint terminal-flag and residual POVM.")),
            Describe.Lean(DescribeId.Create("attainable-auric-loss-interval"),
                DeclarationHandle.Create(Module + "auricLoss_attainable_eq_Icc"),
                H("Every value in the sharp closed loss interval is attainable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("The earlier CoordinatePinching theorem gives loss (2/N) Σ_{b<d} A_b A_d where A_b is the sum of amplitudes in block b. Nonnegativity and Cauchy–Schwarz give √q_b ≤ A_b ≤ √(r_b q_b). Substitute the lower or upper bounds simultaneously into the cross-block products for the two sharp endpoints.")),
                    Paragraph(Text("Place the mass of each nonempty fiber on one coordinate for the lower endpoint, or distribute it uniformly for the upper endpoint. Square the endpoints' amplitudes, interpolate the squared profiles linearly, then take coordinatewise square roots. The path preserves q and its loss is continuous. Empty fibers carry zero weight and the intermediate value theorem supplies every intermediate loss."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-endpoint-renyi"),
                DeclarationHandle.Create(Module + "lower_endpoint_renyi"),
                H("The sparse endpoint is given by order-one-half Rényi entropy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With Σ_b q_b = 1, expanding (Σ_b √q_b)² leaves one plus twice the cross-block products. Hence the sparse endpoint is (exp(H_{1/2}(q)) − 1)/N, where H_{1/2}(q) = 2 log(Σ_b √q_b) in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-entropy-distinct-recorded-scores"),
                DeclarationHandle.Create(Module + "equal_entropy_coherent_different_recorded"),
                H("Equal entropy and coherent success admit distinct recorded optima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("Use the same four Walsh labels and partition into two pairs. Combining amplitudes (A ± √(1 − A²))/2 in a pair gives squared mass 1/2 and sum A. The two choices of block sums are (7/8, 7/8) and (15/16, 13/16). Both give q = (1/2, 1/2), actual pinched entropy log 2 and coherent optimum 49/64. The sharp recorded optima are 49/128 and 197/512, a difference of 1/512.")),
                    Paragraph(Text("The example separates single-shot decoding optima at fixed observed probabilities and entropy. Eldar and Forney, arXiv:quant-ph/0005132v2, Theorem 4 on PDF p. 35, give the square-root optimum for geometrically uniform pure states. Eldar, Megretski and Verghese, arXiv:quant-ph/0205178v1, sections 3.1–3.2, equations (14)–(20) on PDF pp. 9–10, give the finite discrimination dual used by CoordinatePinching. The Walsh profiles and the attainable interval are the deductions here."))),
                DescribeRole.Theorem))));
}
