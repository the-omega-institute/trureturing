using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class GibbsBathBandwidthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/GibbsBathBandwidth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp minimum energy range for finite Gibbs-bath preparation from a maximally mixed memory.",
        H("Minimum Gibbs bath bandwidth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gibbs-marginal-interval"),
                DeclarationHandle.Create(Module + "marginal_bounds"),
                H("Two-sided bounds on the retained marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2011hilbert"), LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("Let the memory dimension be d, the bath dimension be b and the bath input be a Gibbs state with extreme probabilities τ_min and τ_max. The initial memory is maximally mixed. Unitary conjugation preserves the matrix order interval of the product input, and tracing out the bath gives (b/d)τ_min I ≤ ρ ≤ (b/d)τ_max I.")),
                    Paragraph(Text("The ratio bound specializes positive-map contraction in Hilbert’s projective metric. The Lean argument proves the two endpoint inequalities directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermal-bandwidth-obstruction"),
                DeclarationHandle.Create(Module + "thermal_bandwidth_lower_bound"),
                H("Bandwidth and bath dimension bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/allahverdyan2011thermodynamic"), LibraryNoteRef.Create("D5/L/Entropy/reeb2011hilbert"), LibraryNoteRef.Create("D5/L/Entropy/clivaz2019unifying")),
                Blocks(
                    Paragraph(Text("At inverse temperature β > 0, an arbitrary finite Hermitian bath Hamiltonian of energy range W that prepares a positive definite target must satisfy βW ≥ log(μ_max/μ_min) and b ≥ dμ_max, where μ_min and μ_max are the target eigenvalue extremes.")),
                    Paragraph(Text("The binary case follows from exact optimization over reservoir spectra for a maximally mixed target qubit. The bandwidth in this theorem is the range of the entire bath used in one joint unitary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-bath-alignment"),
                DeclarationHandle.Create(Module + "matching_bath"),
                H("The aligned Gibbs state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("In the eigenbasis of a positive definite trace-one target, choose energies −β⁻¹ log μ_i. The normalized Gibbs state in that basis equals the target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-swap-attains-width"),
                DeclarationHandle.Create(Module + "bandwidth_attained"),
                H("The swap attains the spectral bandwidth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved"), LibraryNoteRef.Create("D5/L/Entropy/allahverdyan2011thermodynamic")),
                Blocks(
                    Paragraph(Text("A bath indexed by the memory basis suffices. The tensor swap outputs the target on the memory and the maximally mixed state on the bath. The chosen energies have range β⁻¹ log(μ_max/μ_min)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermal-matrix-exponential"),
                DeclarationHandle.Create(Module + "thermalState_eq_gibbsBath"),
                H("The normalized matrix exponential has Gibbs eigenweights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("The repository thermal-state definition for a finite Hermitian Hamiltonian agrees with its diagonal Gibbs weights conjugated by the Hamiltonian eigenbasis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermal-bandwidth-attainment"),
                DeclarationHandle.Create(Module + "thermal_bandwidth_attained"),
                H("The Hermitian bath attains the lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("Conjugating the matching diagonal Hamiltonian into the eigenbasis of the target gives the minimizing physical matrix Hamiltonian. Its normalized matrix exponential supplies the input bath for the swap."))),
                DescribeRole.Theorem))));
}
