using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseRecordMemoryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseRecordMemory.";
    private static LibraryNoteRef PhyslibDual =>
        LibraryNoteRef.Create("D5/L/QuantumChannels/meiburg2025physlibdual");

    private static LibraryNoteRef DetectorDual =>
        LibraryNoteRef.Create("D5/L/Entropy/eldar2003detectors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The phase-decoding dual gap controls the success of decoding through a finite CPTP memory.",
        H("Finite memory for flat phase records"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-dual-gap"),
                DeclarationHandle.Create(Module + "phaseDual_gap"),
                H("The dual slack dominates the complement of a normalized phase row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DetectorDual),
                Blocks(
                    Paragraph(Text("Let N be the nonzero carrier size, t the real amplitude profile, S its sum, and m a nonnegative lower bound for all amplitudes. For a row with unit-modulus entries, let P be the projection onto that normalized phase row. The unscaled diagonal dual slack dominates S m (I − P) in positive-semidefinite order. Multiplying by the uniform prior 1 / N gives the coefficient S m / N.")),
                    Paragraph(Text("Eldar, Megretski and Verghese formulate the finite discrimination dual in Eqs. (15)–(18) and its complementary slackness in Eqs. (19)–(20) of arXiv:quant-ph/0205178. The phase estimate compares the slack to the complementary projection by subtracting a common lower bound from the amplitudes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phase-memory-success-bound"),
                DeclarationHandle.Create(Module + "phase_success_le"),
                H("Two upper bounds for success through a finite CPTP memory"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(PhyslibDual, DetectorDual),
                Blocks(
                    Paragraph(Text("Let t have sum of squares one, g = S² / N, and M be the encoder output dimension. For any nonnegative lower bound m on the amplitudes, every CPTP encoder and output POVM give uniform success at most min(M / N, g − (1 − M / N) S m). For a nonnegative profile, substitute m = minᵢ tᵢ. The phase entries need only have unit modulus for this upper bound.")),
                    Paragraph(Text("The proof uses the Physlib matrix-map trace dual to pull back the POVM. Positivity and unitality preserve the POVM constraints, and the trace-one output states give the dimension estimate. The prior-art search for this packet found no statement of the explicit phase-memory penalty for arbitrary CPTP encoders and final POVMs.")),
                    Paragraph(Text("For AURIC, let the preprocessing encoder output an M-dimensional register and let the fixed ProjectiveTree.flaggedChannel act on it. A final effect Dₓ on the binary terminal flag and residual register pulls back to the effect flaggedChannel* (Dₓ) on the M-dimensional register. These effects form a POVM with the same success probability by trace duality, so the bound uses the preprocessing dimension M even though the flagged output has dimension 2M. At equal amplitudes a one-leaf tree with identity unitary and fixed flag permits the orthogonal saturation construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phase-memory-optimum-threshold"),
                DeclarationHandle.Create(Module + "phase_optimum_attainable_iff"),
                H("Positive orthogonal phase profiles require the full carrier dimension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DetectorDual),
                Blocks(
                    Paragraph(Text("Assume the flat phase matrix has column Gram matrix N times the identity and every amplitude is positive. A CPTP encoder and output POVM attain the full-carrier guessing probability exactly when the output dimension is at least N. The forward implication uses the strictly positive dual gap. An isometric encoder realizes the converse.")),
                    Paragraph(Text("For these linearly independent pure signals, the prior-weighted Gram square root has constant diagonal S / N. Sasaki, Kato, Izutsu and Hirota give the resulting square-root measurement criterion in §II, Theorem 1 of arXiv:quant-ph/9801012.")),
                    Paragraph(Text("The exact threshold also follows from published ingredients. Kennedy’s uniqueness theorem on the signal span (MIT RLE Quarterly Progress Report 113, pp. 129–130) forces any POVM pulled back from an optimum-preserving encoder to equal the phase PVM. The encoded phase basis tests can then be distinguished perfectly, which forces M ≥ N by the one-shot dimension bound, the uniform-label case of the bound in Nayak’s Theorem 2.4(2). Measuring the phase PVM and storing its outcome in N orthogonal states gives the reverse implication."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthogonal-phase-memory-saturation"),
                DeclarationHandle.Create(Module + "orthogonal_phase_success_attains_dimension"),
                H("Equal amplitudes attain the dimension bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For normalized orthogonal phase rows and a memory with 1 ≤ M ≤ N, an encoder retains M orthogonal labels and resets the complementary subspace to a fixed memory state. A labelled POVM attains uniform success M / N."))),
                DescribeRole.Theorem))));
}
