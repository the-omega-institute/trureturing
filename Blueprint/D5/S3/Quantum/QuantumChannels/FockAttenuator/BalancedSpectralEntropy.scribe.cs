using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class BalancedSpectralEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedSpectralEntropy.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024nongaussian");
    private static readonly LibraryNoteRef PriorOnePhoton = LibraryNoteRef.Create("D5/L/Entropy/he2026energy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native extended spectral entropy inherits the physical half-cap floor.",
        H("The same density operator and its extended spectral entropy"),
        Blocks(
            Paragraph(Text("The balanced one-photon all-density spectral minimum and attainment by every coherent input are already proved in "), Ref(PriorOnePhoton.Value), Text(", Theorem 2 (PDF page 5) and Appendix A.2-A.3 (PDF pages 18-19). This attributed formalization preserves that physical result. No new literature resolution or priority for the odd-occupation application is claimed.")),
            Paragraph(Text("Entropy means QuantumLogEnergy.spectralEntropy from TraceClass.SpectralEnergy: on its native complete eigenbasis it is the ENNReal sum of ENNReal.ofReal(-lambda*log(lambda)). The zero contribution is zero, the complete zero eigenspace is retained, and infinite entropy is allowed. Natural logarithms give nats. FockAttenuator.Entropy.vonNeumannEntropy is a separate basis-infimum API; no equality with that API is assumed or proved here.")),
            Paragraph(Text("The physical operator correspondence is definitional: (densityReference rho).1.1 = rho.operator. The trace-class and trace proof fields are derived from the actual positive trace_one occupation sum. They add no hypothesis to the density domain. The general spectral helpers and odd-occupation derivation are repo-derived from the native spectral suppliers; the exact one-photon floor is literature-attested. The proofs use no assumed minimization theorem.")),
            Node("densityReference", "The density-to-reference adapter",
                "For every Attenuator.DensityOperator rho, densityReference rho is the native positive trace-class contraction Reference Fock whose underlying operator is exactly rho.operator. The occupation Hilbert basis and CFC.abs_of_nonneg prove IsTraceClass; trace_on_basis and summable real-part transport give actual real trace one. The existing density_le_one proves contraction. Unfolding this definition gives the exact operator equality.", DescribeRole.Definition),
            Node("spectral_entropy_lower_of_half", "A trace-one half cap forces the spectral floor",
                "For every complete complex Hilbert space H and every native Reference H T, actual real trace one and T.1.1 <= ((1/2 : Real) : Complex) smul identity imply ENNReal.ofReal(Real.log 2) <= spectralEntropy T. Testing the operator cap on each native unit eigenvector gives lambda <= 1/2. diagonal_hasSum supplies the genuine unconditional HasSum of eigenvalues equal to one. Each positive lambda satisfies -lambda log(lambda) >= lambda log(2); zero is handled separately. Termwise ENNReal comparison and the trace-one sum give the floor even if entropy is infinite."),
            Node("balanced_odd_spectral_entropy_lower", "Every odd-occupation density output has the floor",
                "For every n : Nat with Odd n and every actual density rho, ENNReal.ofReal(Real.log 2) <= spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment n) rho)). The actual physical cap and output trace feed the general spectral theorem. The adapter has exactly the operator attenuatorOperator (1/2) balanced (pointMassEnvironment n) rho. No support, rank, energy or entropy assumption occurs, and the odd-occupation floor asserts no attainment."),
            Node("balanced_one_photon_spectral_entropy_lower", "The consumed one-photon specialization",
                "For every density rho the preceding floor holds with pointMassEnvironment 1. This specializes the odd-occupation theorem and is consumed by both minimization theorems in BalancedAttainment. The occupation one satisfies the oddness hypothesis.", provenance: AssessedProvenance.FromLiterature(PriorOnePhoton)),
            Node("density_entropy_eq_log_two_of_square", "A half-projection polynomial gives exact entropy",
                "For every actual density rho, if rho.operator * rho.operator = ((1/2 : Real) : Complex) smul rho.operator, then spectralEntropy (densityReference rho) = ENNReal.ofReal(Real.log 2). Applying this operator polynomial to each native eigenvector proves lambda=0 or lambda=1/2; the actual trace-one sum then gives equality. No spectrum, rank or entropy equality is assumed. BalancedAttainment proves the polynomial for its actual outputs before applying this criterion; the premise does not assume the minimum-output conclusion."))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) => Describe.Lean(
        DescribeId.Create("fock-balanced-spectral-entropy-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        provenance ?? AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
}
