using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.DiagonalDiscord;

internal sealed class DiagonalDiscordMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/liutakagilloyd2019diagonaldiscord");
    private static readonly LibraryNoteRef GourMarvianSpekkens =
        LibraryNoteRef.Create("D5/L/Entropy/gourmarvianspekkens2009referenceframe");
    private static readonly LibraryNoteRef HuFan =
        LibraryNoteRef.Create("D5/L/Entropy/hufan2016extracting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal discord is nonincreasing under every local quantum channel on the measured subsystem that preserves classical–quantum states. Both optimized entropy gains are attained.",
        H("Monotonicity of diagonal discord in finite dimensions"),
        Blocks(
            Paragraph(Text(
                "Conjecture 1 of Liu, Takagi and Lloyd asserts monotonicity under every local discord-nongenerating channel on the measured qubit. "
                + "It appears in journal Section 3.2.2, p. 9, and arXiv v2 Section III.B.2, p. 6. "
                + "The definitions in equations (2) and (8) include all rank-one eigenbasis measurements within degenerate eigenspaces. Specializing the attained comparison to a two-dimensional measured subsystem gives the inequality of Conjecture 1.")),
            Definition("pinch", "Projective pinching",
                "Pinching is the completely positive trace-preserving map obtained by forgetting the outcome of a complete projective measurement."),
            Theorem("supportContained_pinch", "Support of the pinched state",
                "A vector annihilated by the pinched state makes the sum of nonnegative compressed quadratic forms zero. Each term then vanishes, and completeness of the projections puts the vector in the nullspace of the input."),
            Theorem("finiteTraceLogRelativeEntropy_pinch", "Entropy gain of pinching",
                "The relative entropy from a state to its pinching equals the gain in von Neumann entropy. Input support is contained in the pinched support, so the finite trace-log expression applies to singular states."),
            Theorem("extendedQuantumRelativeEntropy_pinch_pythagoras", "Relative entropy at a fixed reference",
                "For a reference fixed by the pinching and containing the input support, the divergence to that reference splits into the pinching gain and the divergence from the pinched state to the reference. "
                + "The output support condition follows from data processing. The logarithm of the fixed reference commutes with the projections, so the trace cross term is unchanged. "
                + "This is the fixed-projective case of Gour, Marvian and Spekkens, arXiv:0901.0943v2, Theorem 3, equations (9)–(15).", GourMarvianSpekkens),
            Definition("localPVM", "Local basis projections",
                "Each projection onto a column of the measured-side unitary is tensored with the identity on the second subsystem."),
            Definition("localChannel", "Local channel",
                "Tensoring the measured-side Kraus operators with the second identity defines the extension of the channel to the joint state."),
            Theorem("localChannel_apply", "Joint Kraus action",
                "The joint channel applies the Kraus sum with each operator acting on the first factor and the identity acting on the second."),
            Theorem("marginalRight_localChannel", "Locality and the marginal",
                "Tracing out the second factor after the local action gives the same first marginal as applying the measured-side channel after the trace."),
            Definition("Eligible", "Eligible eigenbases",
                "A basis is eligible when the actual first marginal is diagonal in it."),
            Definition("IsCQ", "Classical–quantum states",
                "A state is classical–quantum when it is fixed by some rank-one local pinching. Its off-diagonal first-coordinate blocks vanish in that basis."),
            Definition("PreservesCQ", "Preservation of classical–quantum states",
                "Every classical–quantum input is sent to a classical–quantum output."),
            Definition("basisGain", "Entropy gain in one basis",
                "The gain is the entropy of the pinched joint state minus the input entropy."),
            Definition("diagonalDiscord", "Diagonal discord",
                "The quantity is the infimum of the entropy gain over eligible bases. "
                + "Hu and Fan's Eq. (6), arXiv v2, p. 2, gives the same quantity by taking relative entropy in their B-side measurement-induced disturbance, swapping A and B, and converting bits to nats. "
                + "Their Theorem 1, Eq. (8), bounds steering-induced coherence by that disturbance.", HuFan),
            Theorem("pointwise_transfer", "Transfer with a nonnegative residual",
                "For every eligible input basis, send the pinched input through the channel to obtain a classical–quantum reference. Its first marginal equals the actual output marginal, so a classical basis for the reference is eligible for the output. "
                + "The gain in this output basis plus the nonnegative relative entropy from the pinched output to the reference is bounded by the input gain. "
                + "Data processing gives the upper bound after the fixed-reference decomposition."),
            Theorem("diagonalDiscord_localChannel_mono", "Monotonicity of the optimized gain",
                "The pointwise transfer bounds the output infimum by every eligible input value. Taking the input infimum proves monotonicity for all joint states and all local channels preserving classical–quantum states."),
            Theorem("diagonalDiscord_attained", "Existence of a minimizing eigenbasis",
                "The eligible eigenbases form a nonempty closed subset of the compact unitary group. The entropy gain is continuous by the functional calculus of the continuous scalar function minus x log x, including at zero."),
            Theorem("diagonalDiscord_localChannel_mono_attained", "Comparison of attained minima",
                "There are eligible minimizing eigenbases for the input and output, and the minimum output gain is at most the minimum input gain. The comparison holds in arbitrary finite dimensions.")),
        []));

    private static DocumentBlock.Describe Definition(
        string name, string title, string text, params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create("diagonal-discord-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo([Source, .. acknowledgements]), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string name, string title, string text, params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create("diagonal-discord-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo([Source, .. acknowledgements]), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
