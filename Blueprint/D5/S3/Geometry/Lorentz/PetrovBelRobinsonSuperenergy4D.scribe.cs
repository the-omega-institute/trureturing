using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class PetrovBelRobinsonSuperenergy4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/senovilla2000superenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Weyl quartic, its projective principal directions, and the spinor form of gravitational superenergy.",
        H("Petrov invariants and Bel–Robinson superenergy"),
        Blocks(
            Paragraph(Text("The symmetric four-spinor pairs with its complex conjugate, with one Hermitian Pauli matrix inserted in each slot. A future causal slot is a sum of two rank-one spinor matrices. Expanding all four such sums turns the combined contraction into a sum of squared moduli.")),
            Paragraph(Text("The binary quartic helper proves symmetry under each permutation of the four spinor slots, equivariance of the spinor form under the matrix action, and determinant exponents four and six for the quadratic and cubic invariants. For determinant one, both invariants and their discriminant are fixed. At a double principal direction the discriminant vanishes, and at a triple direction both invariants vanish. The finite and infinite projective charts both enter these conclusions.")),
            Paragraph(Text("The canonical D and II representatives have invariants three times the middle coefficient squared and minus its cube. The III and N representatives and the zero spinor have both invariants zero. For the symmetric I representative with end coefficient a and middle coefficient b, the discriminant is a squared times the square of a squared minus nine b squared. The I representative has nonzero discriminant when a is nonzero and differs from both three b and minus three b.")),
            Paragraph(Text("The D representative has a double direction in each of the two standard charts. The II representative with both coefficients nonzero has a double direction at infinity and two distinct simple finite directions. The III representative has a triple direction at infinity and a simple direction at zero. The N representative has a quadruple direction at infinity. The O polynomial vanishes identically.")),
            Entry("null-screen", "weyl_spinor_null_screen", "The Weyl spinor on the finite null screen",
                "The symmetric spinor induced by a Weyl curvature has the same value on four copies of the column with entries z and one as the complex null-screen tide at z."),
            Entry("canonical-curvatures", "petrov_coulomb_and_wave_spinors", "Coulomb and plane-wave spinors",
                "The Schwarzschild curvature in the given screen has only the middle coefficient, equal to four times mass divided by radius cubed. The plane-wave curvature after the determinant-one chart inversion has only the last coefficient, equal to minus four times the wave amplitude."),
            Entry("chiral-components", "weyl_spinor_electric_magnetic", "Electric and magnetic curvature components",
                "In the chosen screen orientation form the chiral matrix by subtracting the imaginary unit times the magnetic matrix from the electric matrix. Writing Q for this matrix and i for the imaginary unit, the five components in order are 2(Q00 − Q11) − 4iQ01, 2Q02 − 2iQ12, −2(Q00 + Q11), −2Q02 − 2iQ12, and 2(Q00 − Q11) + 4iQ01."),
            Entry("symmetry-and-reality", "belRobinson_totally_symmetric_and_real", "Reality and symmetry in every slot",
                "The complex contraction has zero imaginary part. Every permutation of the four vector arguments preserves it, and its real part is the evaluation of the associated real multilinear map."),
            Entry("metric-trace", "belRobinson_completely_traceless", "All metric traces vanish",
                "For any two distinct slots, substitute each coordinate vector into both slots and sum the resulting contractions with weights minus one in the time coordinate and one in the spatial coordinates. The result is zero for all values in the other two slots."),
            Entry("chiral-phase", "belRobinson_so2_duality_invariant", "Invariance under chiral phase rotations",
                "Multiplying the Weyl spinor by the exponential of the imaginary unit times a real angle preserves the contraction in all four vector arguments."),
            Entry("rest-energy", "belRobinson_superenergy_positive_definite", "Positive definite rest-frame superenergy",
                "With all four arguments the unit time vector, the superenergy is the sum of the five squared coefficient moduli with weights one, four, six, four and one. It is nonnegative and vanishes exactly when the spinor is zero."),
            Entry("curvature-energy", "belRobinson_electric_magnetic_density", "Rest energy from the Weyl matrices",
                "In the null-screen normalization, the density of the spinor of a Weyl curvature is sixteen times the sum of the traces of the squared electric and magnetic matrices."),
            Entry("causal-spinors", "future_causal_spinor_decomposition", "Rank-one decomposition on the future causal cone",
                "If the time coordinate is nonnegative and its square dominates the squared spatial norm, the Pauli matrix of the vector admits a sum of two rank-one spinor matrices. The formula uses a positive first diagonal pivot or, for a vanishing first diagonal, the remaining single diagonal entry."),
            Entry("pauli-positive-semidefinite", "pauli_positive_semidefinite_iff", "The Pauli image of the future causal cone",
                "The Hermitian Pauli matrix of a vector is positive semidefinite exactly when that vector is future causal."),
            Entry("dominant-superenergy", "belRobinson_dominant_superenergy_condition", "Dominance for independently chosen causal vectors",
                "When each of the four vector arguments is future causal, the real contraction is nonnegative."),
            Entry("super-poynting-bound", "belRobinson_super_poynting_bound", "Sharp super-Poynting bound",
                "The sum of the three squared super-Poynting components is bounded above by the square of the rest-frame superenergy."),
            Entry("type-n-and-d-flux", "belRobinson_typeN_and_typeD_flux", "Canonical wave and Coulomb flux",
                "For the canonical type N spinor the density is the squared modulus of its coefficient. The first two flux components vanish and the third is minus the density, so the flux has norm equal to the density. The canonical type D spinor has density six times the squared modulus of its middle coefficient and zero flux."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
