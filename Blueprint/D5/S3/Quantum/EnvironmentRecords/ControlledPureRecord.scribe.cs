using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.EnvironmentRecords;

internal sealed class ControlledPureRecordDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord";
    private const string Title = "Controlled pure records and address dephasing";
    private static LibraryNoteRef DiamondSource =>
        LibraryNoteRef.Create("D5/L/QuantumChannels/watrous2009completelybounded");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact operational distance between controlled readout and complete address dephasing.",
        H(Title),
        Blocks(
            Paragraph(Text(
                "The address is Fin 2. Each record Wᵢ is a matrix of amplitudes with finite "
                + "visible row index O and hidden column index E. Normalization means "
                + "tr(WᵢWᵢ†) = 1 for each address. Write C = W₀W₁† for the cross reduction. "
                + "The second preparation stores an additional orthogonal copy of the address "
                + "in the hidden register.")),
            Claim("controlledIsometry_isometry", "The controlled preparation is isometric",
                "With both records normalized, V sends |i⟩ to |i⟩ tensored with its record vector "
                + "and satisfies V†V = I in address, visible, hidden order."),
            Claim("readoutMap_eq_partialTrace", "Trace out the hidden register",
                "The output on the address and visible register is the partial trace of VXV† over E "
                + "for every address matrix X."),
            Claim("readoutChannel_apply", "The ordinary channel implements the readout map",
                "For normalized records and a visible index with decidable equality, readoutChannel "
                + "is the canonical completely positive trace-preserving channel. Its matrix action is readoutMap."),
            Claim("readoutMap_apply", "The address blocks of the joint output",
                "The (i,j) address block of the readout is Xᵢⱼ WᵢWⱼ†. In particular the (0,1) "
                + "block is X₀₁ C, and the (1,0) block is X₁₀ C†."),
            Claim("dephased_apply", "An orthogonal hidden address copy dephases the readout",
                "If both records have the same visible reduction R, the copy readout gives "
                + "diagonal blocks Xᵢᵢ R and zero off-diagonal blocks."),
            Claim("visible_agreement", "The visible register has the same output",
                "Under the common-reduction hypothesis, tracing out the address from either "
                + "readout gives tr(X) R for every X. A trace-one input therefore gives R in both cases."),
            Claim("trace_visible_apply", "The address alone retains the scalar overlap",
                "Tracing out the visible register multiplies each input entry Xᵢⱼ by tr(WᵢWⱼ†). "
                + "The trace of C is the scalar factor on the (0,1) address entry."),
            Claim("referenceDifference_norm", "Exact norm of the reference-amplified difference",
                "For normalized records, a finite reference with decidable equality, and every complex "
                + "joint matrix X, the output difference has trace norm ‖C‖₁(‖X₀₁‖₁ + ‖X₁₀‖₁). "
                + "Here X₀₁ and X₁₀ are matrices on the reference. The output has only off-diagonal "
                + "address blocks, given by tensoring these input blocks with C and C† respectively."),
            Claim("referenceDifference_le", "Uniform induced trace-norm bound",
                "At each such finite reference dimension, the amplified output difference has trace norm "
                + "at most ‖C‖₁‖X‖₁ for every joint matrix X. Half the difference of X and its "
                + "conjugate by the diagonal address sign is its off-diagonal part. "
                + "The triangle inequality bounds its norm by ‖X‖₁."),
            Claim("readoutDifference_plus", "The balanced address input attains the separation",
                "The projector onto (|0⟩ + |1⟩)/√2 produces output difference of trace norm ‖C‖₁ "
                + "without a reference."),
            Claim("referenceDifference_product", "Every reference state gives an attaining product input",
                "For normalized records, the product of any finite reference density state and "
                + "the balanced address projector attains the amplified bound."),
            Claim("diamondDistance_readout_dephased", "Exact unhalved diamond distance",
                "For normalized records, the diamond distance between the readout channel and its "
                + "hidden-address-copy version is ‖C‖₁. The finite-channel distance takes the supremum "
                + "of output trace-norm differences on joint density inputs over all finite reference "
                + "dimensions. The uniform bound and balanced input give equality. Watrous supplies "
                + "the norm and channel-discrimination framework.",
                AssessedProvenance.FromRepo(DiamondSource)),
            Claim("reconstruction_lower", "A common reconstruction has a worst-case error",
                "On the balanced address input, any single matrix proposed for both joint outputs "
                + "has maximum trace-norm error at least ‖C‖₁/2 by the triangle inequality."),
            Paragraph(Text(
                "These are static finite channels. Physical dynamics and any heat or work assertion "
                + "require separate assumptions.")))));

    private static DocumentBlock Claim(string name, string title, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("controlled-pure-record-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
