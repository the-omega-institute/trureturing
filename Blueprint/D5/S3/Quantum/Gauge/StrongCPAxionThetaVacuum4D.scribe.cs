using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class StrongCPAxionThetaVacuum4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/StrongCPAxionThetaVacuum4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/grillidicortona2016qcdaxion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-flavor strong CP vacuum, the axion mass and quartic coupling, and the winding-number vacuum count.",
        H("Strong CP vacua and the two-flavor axion potential"),
        Blocks(
            Paragraph(Text("The leading chiral mass potential reduces to a linear functional on the unit three-sphere of determinant-one unitary matrices. Its two nonzero coordinate coefficients fix the vacuum energy and, if their squared norm is positive, the unique minimizing field. The chiral model and the separate dilute instanton cosine have the same minimizing angle lattice.")),
            Definition("theta-chiral-potential", "thetaChiralPotential", "Chiral potential with a theta angle",
                "Multiply the diagonal mass matrix by the complex phase with angle theta divided by two. The potential is the real trace of its product with the chiral field times minus the chiral constant and the squared pion decay constant."),
            Definition("theta-energy", "qcdThetaEnergy", "Minimized chiral energy",
                "The energy is minus the chiral constant and squared pion decay constant times the square root of the sum of squared quark masses and twice their product times the cosine of theta."),
            Definition("theta-bar", "thetaBar", "Lifted strong CP angle",
                "Add the theta angle to a real lift of the determinant phase of the quark mass matrix."),
            Entry("chiral-potential-at-zero", "thetaChiralPotential_zero_eq_chiralPotential", "Zero-angle chiral potential",
                "At zero angle the complex phase is one, and the theta-dependent potential agrees with the two-flavor chiral potential."),
            Entry("theta-bar-rotation", "thetaBar_chiral_rotation_invariant", "Strong CP angle under phase rotations",
                "Phasing the two masses multiplies their determinant by the phase of the sum of the angles. Translating theta by minus this sum preserves the lifted strong CP angle. Multiplying a field on the left by opposite diagonal phases preserves its determinant. A common phase multiplies the determinant by the phase of twice the shared angle, and the corresponding compensating translation preserves the lifted angle."),
            Entry("su2-lower-bound", "thetaChiralPotential_ge_qcdThetaEnergy", "Lower bound over all chiral fields",
                "For positive chiral constant and pion decay constant, every determinant-one unitary field has potential at least the stated vacuum energy. This bound holds for all real masses and angles."),
            Entry("diagonal-attainment", "qcdThetaEnergy_attained_on_diagonal_su2", "Explicit unique diagonal minimizer",
                "For positive chiral constant and pion decay constant and positive radicand, divide the mass sum times the half-angle cosine and the down-minus-up mass difference times the half-angle sine by the square root of the radicand. These give the real and imaginary parts of the first diagonal entry, with its conjugate in the second entry. Exactly that field attains the vacuum energy."),
            Entry("massless-quark", "massless_quark_theta_unobservable", "Angle-independent massless-quark vacuum",
                "For positive chiral constant, pion decay constant and down-quark mass, the energy at vanishing up-quark mass is minus the chiral constant times the squared pion decay constant times the down-quark mass. The diagonal field with phases plus and minus half the angle in the up and down entries attains this value for every angle."),
            Entry("cp-minimum", "vafa_witten_cp_conserving_minimum", "CP-conserving minimum of the chiral energy",
                "When the chiral constant, decay constant and quark masses are positive, the energy at zero angle is a global minimum. Equality holds exactly when the cosine of the angle is one, equivalently at integer multiples of two pi."),
            Entry("theta-period-and-maximum", "qcdThetaEnergy_periodic_and_even", "Evenness, periodicity and the maximum",
                "For positive chiral constant, decay constant and quark masses, the vacuum energy is even and has period two pi. At pi it attains its global maximum, which is minus the chiral constant times the squared decay constant and the absolute mass difference."),
            Entry("dashen-cusp", "dashen_degenerate_cusp_and_spontaneous_cp_breaking", "Equal-mass degeneracy and cusp",
                "For equal positive masses and positive chiral constant and decay constant, the energy is minus twice the chiral constant times the squared decay constant times the common mass and the absolute half-angle cosine. At pi the potential vanishes on the whole field group, including the pair of adjoint diagonal fields with entries plus and minus the imaginary unit. The right derivative at pi is minus the chiral constant times the squared decay constant times the common mass. The left derivative is its opposite, so the energy is nondifferentiable there."),
            Entry("unequal-mass-smoothness", "nondegenerate_smooth_at_pi", "Differentiability for unequal positive masses",
                "For unequal positive quark masses the radicand stays positive at every angle. The energy is differentiable everywhere, and its derivative vanishes at pi."),
            Entry("topological-susceptibility", "qcd_topological_susceptibility_exact", "Chiral topological susceptibility",
                "At positive decay constant and positive mass sum, the derivative at angle zero vanishes. The second derivative is the chiral constant times the squared decay constant times the mass product divided by the mass sum. Using the pion mass relation, this equals the mass product divided by the squared mass sum times the squared pion mass and squared decay constant."),
            Definition("axion-potential", "axionPotential", "Shifted axion potential",
                "Evaluate the chiral vacuum energy at the fixed angle plus the axion field divided by its decay constant."),
            Entry("pq-relaxation", "peccei_quinn_relaxation_and_axion_mass", "Peccei-Quinn relaxation and axion mass",
                "For positive chiral constant, pion decay constant, axion decay constant and quark masses, the global minima are exactly the fields with effective angle in the integer multiples of two pi. The field given by minus the axion decay constant times the angle offset has effective angle zero. The squared axion mass is the second derivative there. Multiplying it by the squared axion decay constant gives the susceptibility, bounded above by a quarter of the squared pion mass times the squared pion decay constant, with equality exactly at equal quark masses. The axion mass times its decay constant equals the square root of the mass product divided by the mass sum, multiplied by the pion mass and its decay constant."),
            Entry("axion-quartic", "axion_quartic_self_coupling_exact_and_attractive", "Attractive quartic self-coupling",
                "At the relaxed field the fourth derivative is minus the squared axion mass over the squared axion decay constant times the ratio of the sum of squared quark masses minus their product to the squared mass sum. It is negative, strictly above minus the squared axion mass over the squared decay constant, and at most minus one quarter of that positive mass ratio. Equality in the upper bound holds exactly for equal quark masses."),
            Definition("dilute-instanton-potential", "instantonPotential", "Dilute instanton potential",
                "The cosine of topological charge times the theta angle carries a coefficient of minus twice the common weight times the exponential of minus the instanton action divided by the squared coupling."),
            Entry("instanton-bridge", "instanton_dilute_gas_bridge", "Normalized BPST gas potential",
                "At positive weight, radius and coupling, the BPST action is eight pi squared and its charge is one. The exponential action factor is below one. The resulting cosine potential has period two pi and attains its minimum exactly at integer multiples of two pi."),
            Definition("pq-potential", "pqPotential", "Axion potential at integer winding",
                "Evaluate the chiral energy at the angle offset plus the field times the winding number divided by the PQ decay constant."),
            Entry("domain-wall-number", "domain_wall_vacuum_count_and_fa_invariance", "Vacuum count on the PQ circle",
                "For positive chiral parameters and decay constants and positive integer winding, the PQ potential equals the axion potential with effective decay constant given by the PQ constant divided by the winding. All periods are integer multiples of two pi times that effective constant. In any half-open interval of length two pi times the PQ constant, a finite index of size equal to the winding parametrizes the global minima injectively and surjectively. Beginning the interval at the relaxed field gives the expected consecutive lattice representatives. The product of the axion mass and its effective decay constant depends only on the pion and quark parameters."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Definition);
}
