using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.Qubit;

internal sealed class SignedProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/Qubit/SignedProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed qubit profiles",
        H("Signed qubit profiles"), Blocks(
            Definition("contrast", "Signed contrast",
                "For a finite family of qubit amplitudes, sum the outer products of the amplitudes with their conjugates using arbitrary real coefficients."),
            Definition("overlap", "Squared overlap",
                "The squared modulus of the Hermitian inner product of two amplitudes in the family."),
            Definition("gapSq", "Signed overlap discriminant",
                "Subtract four times the sum of weighted overlap deficits over increasing index pairs from the square of the total weight. For unit preparations, this is the squared spectral gap of the contrast."),
            Theorem("gapSq_eq_trace_det", "Signed overlap expansion",
                "For unit preparations, the squared gap is the square of the total weight minus four times the real determinant of the contrast. Expanding the trace of the square gives an ordered sum of weighted overlaps. The overlap deficits have zero diagonal and are symmetric, so each increasing pair contributes twice."),
            Theorem("trace_posPart_contrast", "Trace of the positive part",
                "For arbitrary real weights and unit preparations, the trace of the positive part is half the sum of the total weight and the larger of its absolute value and the square root of the squared gap. The proof applies the positive part to each of the two eigenvalues."),
            Theorem("trace_posPart_contrast_le_of_pair", "Comparison at a single overlap",
                "Compare two unit families at fixed weights and with all increasing-pair overlaps equal except possibly at the selected pair. The second positive-part trace is at least the first whenever the corresponding weight product times (the second squared overlap minus the first squared overlap) is nonnegative."),
            Theorem("phase_minimum", "Minimum overlap at fixed coordinate magnitudes",
                "For any amplitudes with coordinate magnitudes (cos θ, sin θ) and (sin φ, cos φ), the squared overlap is at least sin²(φ−θ) by the reverse triangle inequality for the two terms of the complex inner product. The real amplitudes (cos θ, sin θ) and (sin φ, −cos φ) are unit and have squared overlap sin²(φ−θ) for all angles. When all four prescribed magnitudes are nonnegative, for example when θ and φ lie in [0, π/2], these amplitudes have the prescribed magnitudes and attain the bound."),
            Theorem("trace_posPart_contrast_isGreatest_opposite_phase", "Maximum profile at fixed coordinate magnitudes",
                "Fix e₀ = (1, 0) and angles θ, φ in [0, π/2]. For three real weights with a₀a₂ ≤ 0, the unit triple ((cos θ, sin θ), e₀, (sin φ, −cos φ)) belongs to the domain and its positive-part trace bounds that of every unit triple (u, e₀, v) with coordinate magnitudes (cos θ, sin θ) and (sin φ, cos φ). The two reference overlaps are the squared first-coordinate magnitudes, cos² θ and sin² φ. The minimum-overlap theorem minimizes the outer squared overlap, so the signed single-overlap comparison gives the upper bound. This is the pointwise fixed-basis step in the Gibbs-record upper bound. Changing to the reference basis, integrating the profile, and verifying the global certificate are separate steps."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("signed-qubit-profile-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
