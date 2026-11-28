using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class DiracLandauEulerHeisenberg4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/adler1971photondispersion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Dirac magnetic spin pairing and the weak-field electromagnetic effective action in four dimensions.",
        H("Dirac magnetic levels and the Euler–Heisenberg action"),
        Blocks(
            Paragraph(Text("The transverse Pauli square fixes the coefficient of the magnetic spin shift. The quartic effective action then gives the polarization-dependent probe Hessians. In a purely electric field the vacuum-persistence series exhibits a separate exponential scale.")),
            Entry("zero-magnetic-shift", "dirac_g2_zero_mode_iff", "Exact lowest-level cancellation",
                "At positive magnetic coupling, the shift at oscillator label zero and spin label one half vanishes exactly when the gyromagnetic factor equals two. Equivalently the squared energy at that label equals the sum of squared mass and squared longitudinal momentum exactly at that factor."),
            Entry("level-multiplicity", "dirac_landau_exact_twofold_degeneracy", "Multiplicity of the magnetic levels",
                "For positive magnetic coupling and either permitted spin, attaining the level indexed by a natural number k is equivalent to having oscillator label k and spin one half, or having positive k, oscillator label k minus one, and spin minus one half. Thus level zero has exactly one label and every higher level has two."),
            Entry("pauli-square", "dirac_pauli_square_identity", "Pauli square in a linear magnetic gauge",
                "The upper off-diagonal blocks of the three spatial Dirac matrices are the Pauli matrices. In a complex algebra where the free momenta commute and the first momentum has commutator minus the imaginary unit with position, adding the magnetic position term to the second momentum gives the transverse Pauli square with its unit Zeeman coefficient. The polynomial momentum operators also realize the identity for each Fourier momentum in the second coordinate."),
            Entry("hermite-modes", "dirac_landau_squared_energy_modes", "Hermite modes of the squared magnetic operator",
                "At positive magnetic coupling, every oscillator label and each Pauli spin component give a nonzero translated Hermite mode. The diagonal Pauli entry is minus twice the spin projection used in the energy formula. The squared magnetic operator applied to the mode is pointwise multiplication by the stated squared Landau energy."),
            Entry("lorentz-and-reflections", "euler_heisenberg_lorentz_and_cp_invariance", "Lorentz invariance, reflections and null fields",
                "The action is invariant under determinant-one metric-preserving Lorentz transformations and under the separate changes of sign of the electric and magnetic fields. It vanishes whenever both field invariants are zero."),
            Entry("duality", "euler_heisenberg_breaks_em_duality", "The quartic term under field rotation",
                "The covariant Maxwell stress tensor remains fixed. At twice the rotation angle the first invariant transforms as cosine times the first invariant minus twice sine times the second, and the second as cosine times the second plus half sine times the first. The quartic difference is three quarters of the difference between the first invariant squared and four times the second squared, times the squared sine, plus three times the product of the invariants times sine and cosine. A rotation changing the quartic exists exactly when at least one invariant is nonzero. At angle pi over four a pure magnetic field gives the quartic factor seven quarters and a zero linear Lagrangian."),
            Entry("probe-hessians", "vacuum_birefringence_indices_and_subluminality", "Probe Hessians and refractive index shifts",
                "For positive fine-structure constant, mass and background field with the stated charge relation, write u for the effective quartic coefficient times the squared field. The coefficients of the squared electric and magnetic amplitudes in the second derivative are one plus ten u and minus one plus four u for the parallel mode, and one minus four u and minus one plus twelve u for the perpendicular mode. The squared speeds are the negative magnetic-to-electric Hessian ratios. The two refractive indices have derivatives seven and four at u equal to zero. In critical-field units the first-order shifts are seven and four times alpha divided by ninety pi times the squared field ratio. Their ratio is seven quarters. Both squared speeds lie strictly between zero and one for u below one twelfth, where the parallel squared speed is smaller exactly when u is below three sixty-eighths."),
            Entry("hyperbolic-quartic", "euler_heisenberg_coth_quartic_limit", "Quartic coefficient of the hyperbolic kernel",
                "After subtracting one and the quadratic term from x times its hyperbolic cotangent, division by the fourth power has two-sided punctured limit minus one forty-fifth. In the combined fraction the denominator is the fourth power times the hyperbolic sine."),
            Entry("proper-time-coefficient", "euler_heisenberg_proper_time_quartic_coeff", "Magnetic proper-time moment",
                "For positive mass, the Lebesgue integral of proper time times the exponential of minus mass squared times proper time over the positive half-line is the inverse fourth power of the mass. Multiplying by the magnetic prefactor yields the pure magnetic quartic coefficient of the effective action, with fine-structure constant equal to squared charge divided by four pi."),
            Entry("schwinger-series", "schwinger_pair_production_series_and_essential_singularity", "Electric series bounds and right-hand flatness",
                "For positive charge, mass and electric field the Schwinger summands are summable. The rate lies between the first exponential term times its prefactor and the same exponential times squared charge-field product divided by twenty-four pi. For every natural power of the electric field, dividing the rate by that power yields limit zero at zero from the right."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
