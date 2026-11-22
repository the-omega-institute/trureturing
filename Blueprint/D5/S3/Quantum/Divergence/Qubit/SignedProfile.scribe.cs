using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.Qubit;

internal sealed class SignedProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/Qubit/SignedProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed qubit profiles",
        H("Signed qubit profiles"), Blocks(
            Definition("contrast", "Signed contrast",
                "For a finite family of qubit amplitudes, sum their rank-one matrices with arbitrary real coefficients."),
            Definition("overlap", "Squared overlap",
                "The squared modulus of the Hermitian inner product of two amplitudes in the family."),
            Definition("gapSq", "Squared spectral gap",
                "Subtract four times the sum of weighted overlap deficits over increasing index pairs from the square of the total weight."),
            Theorem("gapSq_eq_trace_det", "Signed overlap expansion",
                "For unit preparations, the squared gap is the square of the total weight minus four times the real determinant of the contrast. Expanding the trace of the square gives an ordered sum of weighted overlaps. The overlap deficits have zero diagonal and are symmetric, so each increasing pair contributes twice."),
            Theorem("trace_posPart_contrast", "Trace of the positive part",
                "For arbitrary real weights and unit preparations, the trace of the positive part is half the sum of the total weight and the larger of its absolute value and the square root of the squared gap. The proof applies the positive part to each of the two eigenvalues."),
            Theorem("trace_posPart_contrast_le_of_pair", "Comparison at a single overlap",
                "Compare two unit families at fixed weights and with all increasing-pair overlaps equal except possibly at the selected pair. The second profile is at least the first whenever the corresponding weight product times the second overlap minus the first overlap is nonnegative."),
            Theorem("gapSq_fin_three", "Three-class discriminant",
                "With squared overlaps (1−X,Y,Z) in pair order (1,2), (1,3), (2,3), the discriminant is (a₃−a₁−a₂)² + 4(−a₁a₂X+a₁a₃Y+a₂a₃Z). This is the polynomial entering the Gibbs-record certificate."),
            Theorem("phase_minimum", "Minimum overlap at fixed coordinate magnitudes",
                "For amplitudes with coordinate magnitudes (cos θ,sin θ) and (sin φ,cos φ), the squared overlap is at least sin²(φ−θ). The real amplitudes (cos θ,sin θ) and (sin φ,−cos φ) are unit and attain equality. The lower bound follows by applying the reverse triangle inequality to the two terms of the complex inner product."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("signed-qubit-profile-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
