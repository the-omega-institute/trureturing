using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class FairProjectiveRecordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/Auric/FairProjectiveRecord.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The measured AURIC class law at the distinguished irrational angle.",
        H("Fair projective records at a fixed horizon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("measured-history-trace"),
                DeclarationHandle.Create(Prefix + "measuredHistory_trace"),
                H("Fair trace weights from the original flagged instrument"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Observer/auricfib2026environmentinstrument")),
                Blocks(Paragraph(Text(
                    "Restrict the original five-level instrument to the code with ordered columns "
                    + "(e₀ + e₃)/√2, (e₁ + e₄)/√2, e₂. Take the angle to be arcsin((√5 − 1)/2). "
                    + "Select each measured flag block after tensoring with the identity on a "
                    + "finite spectator. The corresponding Kraus matrix on the code is the "
                    + "normalized qutrit letter divided by √2. The normalized letters are unitary. "
                    + "A word of length n therefore has trace 2⁻ⁿ on any trace-one joint code "
                    + "and spectator input, and its output is the code embedding of the qutrit "
                    + "conjugation tensored with spectator identity, scaled by 2⁻ⁿ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chronological-fibers"),
                DeclarationHandle.Create(Prefix + "chronological_fibers"),
                H("Equality of the physical and projective fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Observer/auricfib2026environmentinstrument")),
                Blocks(
                    Paragraph(Text(
                        "Chronological tuples put later letters to the left. At each fixed length "
                        + "the physical qutrit products coincide up to a complex scalar exactly "
                        + "when their real plane products give the same point of PGL(2,ℝ). "
                        + "The real letters are A and AW, where d = √((1 + √5)/2), A has rows "
                        + "(d, −d²) and (d² − d, d² − d), and W swaps the two coordinates.")),
                    Paragraph(Text(
                        "Both physical letters act by the same nonzero scalar on (1,1,1), "
                        + "which fixes the phase at equal lengths. After division by the cosine, "
                        + "the entries are integral polynomials in i tan θ reduced modulo "
                        + "X⁴ − X² − 1. The real and imaginary parts recover the four coefficients. "
                        + "The real evaluation at −d also recovers them, by squaring the even and "
                        + "odd parts and using the negative conjugate of the golden ratio. "
                        + "The specialized plane restriction in the basis (1,0,−1), (0,1,−1), "
                        + "together with the known action on (1,1,1), recovers the full matrix.")),
                    Paragraph(Text(
                        "The real determinants are ±1, so the projective scalar is a sign. "
                        + "Reduce the integral quartic coordinates modulo three. Both letters "
                        + "then act by the same unit on (1,1). A negative equality at equal "
                        + "lengths would make twice a power of this unit vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fair-projective-record"),
                DeclarationHandle.Create(Prefix + "fair_projective_record"),
                H("Counted endpoint masses and the finite memory substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Observer/auricfib2026recordshannonrate")),
                Blocks(
                    Paragraph(Text(
                        "The finite class carrier is the image of the normalized chronological "
                        + "qutrit products. Reversal bijects the fair tuples of each length, "
                        + "so pushing the measured class law through the endpoint embedding gives "
                        + "the law of the ordinary left-to-right projective product. The mass of "
                        + "each endpoint in the image is its physical fiber size divided by 2ⁿ. "
                        + "Endpoints outside the image have mass zero. The empty tuple has mass one "
                        + "and gives the identity endpoint.")),
                    Paragraph(Text(
                        "In uniform_record_memory_bounds take the input basis to be Fin n → Bool, "
                        + "the label type to be RecordClass n, and the label map to be classOf. "
                        + "Then N = 2ⁿ, and the mass of a finite set of labels is the sum of their "
                        + "endpoint masses. For target success α = 1 − ε, positive environment "
                        + "dimension e, and 2ⁿ ≤ d_mem e, a minimum-cardinality class cover for "
                        + "these masses supplies M. The full-block and remainder quantities "
                        + "use the same integer fiber counts as the endpoint masses."))),
                DescribeRole.Theorem))));
}
