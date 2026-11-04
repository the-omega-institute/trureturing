using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class InvolutionRootlessLowGradesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/InvolutionRootlessLowGrades.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Production lattice reflection and the literal canonical Sugawara fixed low-energy spaces.",
        H("Actual Theta-Fixed Rootless Low Grades"),
        Blocks(
            Definition("orbits", "NormFourOrbit", "Free negation orbits", "The quotient identifies a norm-four integral charge with its negative. Integral torsion-freeness and the norm equation exclude fixed charges; a constructed equivalence with orbit times Bool proves that the natural shell cardinality is twice the orbit cardinality."),
            Definition("orbit-rep", "normFourOrbitRep", "Orbit representative", "A classical representative is used to write each basis vector. No orientation, enumeration or norm-four count is assumed."),
            Definition("two-config", "TwoConfig", "Actual energy-two configuration coordinates", "For positive definite rootless even LatticeData, the all-charge low-grade basis identifies the literal energy-two labels with a mode-two oscillator, an unordered pair of mode-one colours including repetition, or a norm-four charged ground state."),
            Definition("fixed-index", "FixedTwoIndex", "Fixed energy-two basis indices", "The indices are the unordered neutral pairs and the free norm-four negation orbits. Empty rank and empty shells remain in scope."),
            Definition("coordinate-theta", "coordinateTheta", "Signed coordinate permutation", "This linear endomorphism negates the mode-two neutral coordinates, fixes the neutral pair coordinates and exchanges the two charge coordinates in every negation orbit. Its relation to production theta is proved rather than assumed."),
            Definition("grade-coordinates", "gradeTwoCoordinateEquiv", "Complete actual grade-two coordinates", "For positive definite rootless even LatticeData, gradeTwoBasis gives a linear equivalence from the complete actual grade to the configuration function space. Positivity proves shell finiteness; there is no charge cutoff or replacement carrier."),
            Theorem("theta-conjugacy", "theta_gradeTwo_coordinate_transport", "Production theta conjugacy on the full actual grade", "For every positive definite rootless even LatticeData D and every vector in its actual energy-two grade, production LatticeInvolution.theta is the inverse coordinate equivalence applied to coordinateTheta of that vector's coordinates. The proof checks production theta_single and sigma_monomial on all three basis sectors, then uses basis extensionality."),
            Definition("actual-basis", "actualFixedEnergyTwoBasis", "Basis of the literal canonical fixed L0 eigenspace", "For positive definite rootless even LatticeData, a basis indexed by neutral unordered pairs and norm-four negation orbits is constructed for fixedSpace D intersected with the eigenspace at two of sugawaraMode D (gramComplex D) inverse zero. The coordinate conjugacy identifies the actual intersection with the invariant coordinate space. ActualL0_eigenspace_eq_grade supplies the exact Sugawara bridge. Each neutral basis vector in the actual canonical fixed eigenspace is the zero-charge monomial of the unordered mode-one pair occupation. Repeated colours are included."),
            Theorem("actual-charge-vector", "actualFixedEnergyTwoBasis_charge_coe", "Literal charged orbit basis vectors", "For positive definite rootless even LatticeData, each charged basis vector in the actual canonical fixed eigenspace is the sum of the two charged ground states at the chosen charge and its negative. Independence and spanning come from the constructed equivalence, rather than an orbit dimension assumption."),
            Theorem("actual-fixed-spectrum", "actual_theta_fixed_rootless_low_spectrum", "Actual fixed low-energy spectrum in arbitrary rank", "For every even LatticeData whose real Gram matrix is positive definite and has no integral norm-two charges, the literal production fixedSpace intersections with the canonical inverse-Gram Sugawara L0 eigenspaces at energies zero, one and two have complex finranks one, zero, and choose(rank+1,2) plus Nat.card of the norm-four integral charge shell divided by two. Rank zero is included. The vacuum is fixed, every energy-one oscillator is odd, and energy two uses the constructed free charge-orbit basis. No trace, fixed dimension, shell count or convergence premise is used."),
            Paragraph(Text("The reflection is the phase-one lift on the lattice vertex algebra. The reflection conjugacy relates the all-charge low-grade bases to the fixed orbit basis. Classical mathematical context is Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster, and Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 section 4.1. Mathlib quotient, basis and symmetric-power APIs retain their original authorship and Apache-2.0 license. No literature novelty is claimed.")),
            Paragraph(Text("This constructs low-energy spaces of the existing fixed vertex algebra. It does not construct twisted sectors, an orbifold extension, a Monster action, fusion or anomaly data, string theory or an AdS/CFT bridge.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
