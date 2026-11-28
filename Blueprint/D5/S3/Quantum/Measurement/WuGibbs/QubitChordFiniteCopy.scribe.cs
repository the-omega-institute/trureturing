using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.WuGibbs;

internal sealed class QubitChordFiniteCopyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective readout and pure-endpoint preparation give Bernoulli product bounds on finite-copy qubit trace distance along a closed Bloch chord.",
        H("Finite-copy trace distance on a closed Bloch chord"),
        Blocks(
            Paragraph(Text(
                "Write ρ(t) for the trace-one qubit matrix with Bloch vector m + t e, where m and e are real " +
                "three-vectors, e is a unit vector, and m is perpendicular to e. The physical points satisfy " +
                "‖m + t e‖ ≤ 1. Let ℓ = √(1 − ‖m‖²) be the chord radius and B(t) the sign law " +
                "with probabilities (1 + t)/2 and (1 − t)/2, in that order.")),
            Entry("chord-projector", "chordProjector_isProjective", "Projective measurement along the chord",
                "For every unit Bloch direction e, the qubit matrices with Bloch vectors e and −e form a " +
                "two-outcome POVM whose effects are idempotent. On a physical state ρ(t) the readout has law B(t)."),
            Entry("chord-endpoint", "chordEndpoint_isPure", "Pure endpoint states",
                "If e is a unit vector, m is perpendicular to e, and ‖m‖² ≤ 1, each endpoint matrix ρ(ℓ) and ρ(−ℓ) " +
                "is positive semidefinite, has trace one, and is idempotent."),
            Entry("finite-copy-chord", "finite_copy_chord_comparison", "Two finite-copy bounds",
                "`Wu.QubitChordFiniteCopy.finite_copy_chord_comparison` holds for every natural n and all real a and b " +
                "with ‖m + a e‖ ≤ 1 and ‖m + b e‖ ≤ 1. The trace distance between the actual tensor powers ρ(a)⊗ⁿ " +
                "and ρ(b)⊗ⁿ is at least TV(B(a)⊗ⁿ, B(b)⊗ⁿ) and at most TV(B(a/ℓ)⊗ⁿ, B(b/ℓ)⊗ⁿ), with TV " +
                "the total variation of the sign-string laws. The lower bound reads each copy with the projective measurement " +
                "along e. Grouping the strings on which the first law is at least the second gives a binary outcome " +
                "whose probability gap equals the lower total variation. The upper bound uses mixtures of " +
                "the same tensor products of pure endpoints, with independent signs of means a/ℓ and b/ℓ, respectively. " +
                "The closed chord includes its pure endpoints. When ℓ = 0, both states coincide since a = b = 0, and the normalized means " +
                "are zero under Lean’s real division. For n = 0, there is one empty record and both states are the same " +
                "scalar matrix, so all three distances are zero."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
