using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class DiracHydrogenFineStructure4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/darwin1928waveequations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relativistic hydrogen and the Coulomb shell algebra.",
        H("Relativistic hydrogen and the Coulomb shell algebra"),
        Blocks(
            Paragraph(Text("The attractive Coulomb convention uses positive coupling. The circular tower uses a negative signed angular index, with magnitude equal to the principal quantum number. The fine-structure energy depends on the magnitude of the angular index. Expansion uses squared coupling as its real variable near zero.")),
            Entry("runge-lenz-split-iff", "runge_lenz_split_iff", "Runge–Lenz bracket decomposition",
                "The signed angular and Runge–Lenz commutator identities are equivalent to the two rotation brackets and the vanishing mixed bracket of the half-sum and half-difference generators."),
            Entry("runge-lenz-casimir-identities", "runge_lenz_casimir_identities", "Coulomb Casimir identities",
                "For generator families with each paired angular and Runge–Lenz generator commuting, the sum of their quadratic squares is twice the sum of the two rotation Casimirs. Their mixed product is the difference of the two rotation Casimirs."),
            Entry("bohr-energy-from-casimir", "bohr_energy_from_casimir", "Casimir and Bohr energy",
                "Equality of the nonnegative spin Casimirs forces equal spin. With the principal index equal to twice that spin plus one, the total Casimir is four times the single spin Casimir and equals the principal index squared minus one, yielding the Bohr denominator."),
            Entry("bohr-shell-degeneracy", "bohr_shell_degeneracy", "Orbital shell degeneracy",
                "Summing the odd angular multiplicities below the principal quantum number gives its square."),
            Entry("bohr-spin-shell-capacity", "bohr_spin_shell_capacity", "Spin-resolved shell capacity",
                "Doubling the orbital multiplicities gives twice the square of the principal quantum number."),
            Entry("dirac-subshell-degeneracy", "dirac_subshell_degeneracy", "Dirac angular subshell count",
                "The angular multiplicities occur twice below the maximal angular index and once at the maximum, giving twice the square of the principal quantum number."),
            Entry("dirac-circular-solves-coupled-radial-ode", "dirac_circular_solves_coupled_radial_ode", "Exact circular radial spinors",
                "At positive radius, positive coupling below the angular index gives the two component derivatives and both signed radial equations at the circular energy."),
            Entry("dirac-1s-solves-coupled-radial-ode", "dirac_1s_solves_coupled_radial_ode", "Exact ground radial spinor",
                "At positive radius, the angular index minus one gives the two derivative and radial identities at the square-root ground energy for coupling between zero and one."),
            Entry("dirac-2p-solves-coupled-radial-ode", "dirac_2p_solves_coupled_radial_ode", "Exact first circular excitation",
                "At positive radius, the angular index minus two gives the two derivative and radial identities for coupling between zero and two."),
            Entry("dirac-1s-normalizable-and-small-component-ratio", "dirac_1s_normalizable_and_small_component_ratio", "Normalizability and lower-component size",
                "For positive mass and coupling between zero and one, the absolute component ratio equals the square-root ratio and is less than one. The sum of squared radial components is integrable on positive radii."),
            Entry("dirac-1s-ratio-asymptotic", "dirac_1s_ratio_asymptotic", "Weak-coupling ratio",
                "The ground-state component ratio divided by the positive coupling tends to one half as the coupling approaches zero."),
            Entry("sommerfeld-circular-matches-ode", "sommerfeld_circular_matches_ode", "Circular Sommerfeld energy",
                "For equal principal and angular indices and positive coupling below the angular index, the Sommerfeld value equals the circular radial eigenvalue."),
            Entry("sommerfeld-bound-state-window", "sommerfeld_bound_state_window", "Energy below rest mass",
                "Within the bound-state domain and for positive mass, the Sommerfeld energy is positive and strictly below the rest mass."),
            Entry("sommerfeld-ground-critical-limit", "sommerfeld_ground_critical_limit", "Critical ground energy",
                "The ground energy tends to zero as the coupling approaches one from below."),
            Entry("sommerfeld-strictly-increasing-in-k", "sommerfeld_strictly_increasing_in_k", "Angular fine-structure ordering",
                "At fixed principal index and positive mass and coupling in both domains, the energy increases strictly with the angular index."),
            Entry("sommerfeld-fourth-order-expansion", "sommerfeld_fourth_order_expansion", "Fourth-order fine structure",
                "The squared-coupling energy at zero equals the rest mass. Its first derivative is the Bohr coefficient, and half of its second derivative is the fine-structure coefficient."),
            Entry("sommerfeld-2p-splitting-coefficient", "sommerfeld_2p_splitting_coefficient", "Leading two-p splitting",
                "Half the difference of the squared-coupling second derivatives at principal index two equals the mass divided by thirty-two."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
