using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class QutritPureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/LocalCompression/QutritPure.";

    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");
    private static readonly LibraryNoteRef NayakSen =
        LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible");
    private static readonly LibraryNoteRef Schumacher =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/schumacher1996sendingentanglement");
    private static readonly LibraryNoteRef FarberGour =
        LibraryNoteRef.Create("D5/L/Divergence/farbergour2026classicalcommunication");
    private static readonly LibraryNoteRef ChaParkLee =
        LibraryNoteRef.Create("D5/L/Divergence/chaparklee2026goldilocks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the normalized qutrit Bell state, the least joint trace-distance error among channels supported in a prescribed output plane is 2/3. "
        + "An explicit qubit-memory protocol achieves strictly smaller error.",
        H("Pure qutrit local compression in joint trace distance"),
        Blocks(
            Paragraph(Text(
                "The source is the normalized qutrit Bell state. The reference factor stays untouched. "
                + "Distortion is half the trace norm of the joint state difference. "
                + "The qubit protocol uses one fixed encoder and one fixed decoder, connected solely by the qubit. "
                + "Kato Section VII proposes approximate local compression. Nayak and Sen Theorem 2.1 "
                + "characterizes reversible finite channels. Schumacher Eq. (10) expresses entanglement fidelity "
                + "in terms of Kraus operators. Farber and Gour Theorem 5 gives the exact unassisted root fidelity "
                + "and uses projection with reset to attain it. Cha, Park and Lee Proposition 3.7 exhibits a "
                + "nonisometric-decoder advantage for phase-ensemble fidelity. Their Appendix D treats Haar-average "
                + "fidelity and Appendix L gives bounds for ensemble-average trace distance.")),
            Describe.Lean(
                DescribeId.Create("qutrit-fixed-output-plane-optimum"),
                DeclarationHandle.Create(Prefix + "plane_optimum"),
                H("Exact least distortion with output in a prescribed plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato, NayakSen, FarberGour),
                Blocks(Paragraph(Text(
                    "For every unitary frame, the minimum over CPTP maps into its first two levels is 2/3. "
                    + "In the coordinate frame the effect is the projector onto the normalized vector with coefficients (1, 1, 2) "
                    + "on the matched coordinates. Its expectation on the source is 8/9. "
                    + "With output in the plane, the effect expectation is at most 2/9 by positivity "
                    + "and the uniform Choi reference marginal. Projection to the two kept coordinates "
                    + "with the discarded input reset to level 1 attains the bound. "
                    + "For this channel the difference is bounded above by a positive rank-one matrix of trace 2/3. "
                    + "Conjugating the input and output by a common change of basis acts by unitary "
                    + "congruence on the joint difference, preserving the trace norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-qubit-memory-trace-distance-witness"),
                DeclarationHandle.Create(Prefix + "qubit_memory_witness"),
                H("A strict qubit-memory witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato, Schumacher, FarberGour, ChaParkLee),
                Blocks(Paragraph(Text(
                    "The encoder preserves the plane and resets input level 2 to memory level 1. "
                    + "The decoder uses amplitudes (1, 4/5) on the embedded qubit and sends level 1 "
                    + "to output level 2 with amplitude 3/5 in a second Kraus operator. Both families "
                    + "sum to the identity in their Kraus completeness equations. On the matched "
                    + "coordinates the source-minus-output difference is dominated by the outer product "
                    + "of (60, 73, 107) divided by 31500. The slack is a sum of positive rank-one matrices "
                    + "on the full joint space, including the two unmatched output coordinates. "
                    + "The majorant has trace 10189/15750, strictly below 13/20 and 2/3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-witness-decoder-nonisometric"),
                DeclarationHandle.Create(Prefix + "witness_decoder_not_isometric"),
                H("The witness decoder has no single-isometry representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NayakSen, ChaParkLee),
                Blocks(Paragraph(Text(
                    "The pure input at memory level 1 has output probabilities 16/25 and 9/25 "
                    + "on levels 1 and 2 with zero off-diagonal entries. A single matrix conjugation "
                    + "would send that input to an outer product, whose two diagonal entries multiply "
                    + "to the squared magnitude of the off-diagonal entry."))),
                DescribeRole.Theorem))));
}
