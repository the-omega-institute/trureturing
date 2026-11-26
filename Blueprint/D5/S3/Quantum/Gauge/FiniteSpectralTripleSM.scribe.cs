using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class FiniteSpectralTripleSMDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/FiniteSpectralTripleSM.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite real matrix model for one generation of Standard Model fermions.",
        H("The finite real spectral triple of the Standard Model"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-spectral-triple-ko-six"),
                DeclarationHandle.Create(Prefix + "finite_spectral_triple_ko6"),
                H("The KO-dimension-six identities and both order conditions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/LieTheory/conneschamseddine2007sm")),
                Blocks(Paragraph(Text(
                    "On the 32 complex fermion coordinates, the faithful action of the real algebra "
                    + "preserves the grading. Charge conjugation is an involution, fixes the Dirac "
                    + "operator under conjugation, and negates the grading under conjugation. "
                    + "The grading is self-adjoint and squares to one. The Dirac operator is "
                    + "self-adjoint and anticommutes with the grading. The left and opposite "
                    + "actions commute, and every Dirac commutator for the left action commutes "
                    + "with every opposite action, for arbitrary complex Yukawa and Majorana parameters. "
                    + "The Majorana entry joins the right-handed neutrino to its conjugate. Their "
                    + "left and opposite scalar actions coincide while their grading signs differ, "
                    + "so this representation fails the stronger orientability axiom on that pair. "
                    + "The result concerns the finite real even spectral triple identities."))),
                DescribeRole.Theorem),
            Node("fermion-dimension", "fermion_dimension", "The one-generation dimension",
                "The complex coordinate space has dimension 32. Each of the four chirality and "
                + "charge sectors contains a lepton doublet and a weak doublet with three colors."),
            Node("real-structure", "realStructure_antiunitary", "Antiunitarity",
                "The real structure conjugates a complex affine combination and conjugates the "
                + "coordinate inner product. The particle and antiparticle permutation is bijective."),
            Node("quaternion-special-unitary", "quatMatrix_specialUnitary", "The weak special unitary group",
                "The two-by-two complex quaternion image of the norm-one quaternions is exactly "
                + "the unitary matrices of determinant one."),
            Node("quaternion-inner", "quatMatrix_hs_inner", "The normalized Hilbert–Schmidt inner product",
                "Half the real trace of the adjoint of the first quaternion matrix times the second "
                + "is the real quaternion inner product."),
            Node("weak-independence", "weak_generators_independent", "Independent weak directions",
                "The three imaginary quaternion units have identity Gram matrix. The three-anchor "
                + "criterion then gives real linear independence."),
            Node("represented-determinant", "rep_det", "The unimodular character",
                "On a unitary algebra triple the determinant of the represented unitary is the "
                + "fourth power of the scalar times the color determinant."),
            Node("lift-determinant", "gaugeLift_det", "The determinant of the gauge lift",
                "On every unitary algebra triple the lift has determinant one, since its two "
                + "determinant factors are complex conjugates with product one."),
            Node("unimodularity-witness", "unimodularity_witness", "The reduced character restriction",
                "The unitary with scalar and quaternion entries one and color matrix diag(i, 1, 1) "
                + "has both determinants one and reduced character i."),
            Node("reduced-cover", "reduced_cover", "Parametrization of reduced unitaries",
                "Every unitary triple with scalar times color determinant one comes from the "
                + "cover. Choose a cube root t of the scalar and multiply the original color matrix "
                + "by t. The root is unitary and the new color matrix has determinant one."),
            Node("cover-phases", "lift_particle_phase", "The phases on the cover",
                "The cover uses scalar t cubed and color matrix t inverse times g. The particle "
                + "phases for the neutrino, electron, up quark, down quark, lepton doublet and "
                + "quark doublet have exponents 0, −6, 4, −2, −3 and 1, respectively. The weak "
                + "quaternion matrix acts on the left doublets and the conjugate of g acts on "
                + "quark color."),
            Node("hypercharge", "hypercharge_table", "All-left-handed hypercharges",
                "The all-left-handed charges are the phase exponents divided by six, with the signs "
                + "reversed for the conjugates of right-handed particles. In the order Q, u conjugate, "
                + "d conjugate, L, e conjugate and neutrino conjugate the charges are 1/6, −2/3, "
                + "1/3, −1/2, 1 and 0."),
            Node("anomaly-cancellation", "anomaly_cancel", "Four local chiral anomaly coefficients",
                "The mixed color, mixed weak, mixed gravitational and cubic abelian coefficients "
                + "are zero. The latter two sum over the sixteen all-left-handed coordinates."),
            Node("central-kernel", "cover_kernel_iff", "The central equations for the kernel",
                "For a unitary scalar t, the gauge lift of the cover element is the identity "
                + "exactly when t to the sixth is one, the weak matrix is t cubed times the identity, "
                + "and the color matrix is t to the fourth times the identity."),
            Node("inner-fluctuation", "inner_fluctuation_iff", "Self-adjoint inner fluctuations",
                "The real span of represented elementary one-forms has self-adjoint part given "
                + "by a single quaternion multiplying the lower particle Yukawa block, with its "
                + "adjoint in the upper block."),
            Node("higgs-injective", "higgsForm_injective", "Uniqueness of the Higgs parameter",
                "A nonzero Yukawa coupling determines a full column of the quaternion matrix. Either "
                + "column determines all four real quaternion coordinates."),
            Node("quadratic-moment", "trace_dirac_sq", "The quadratic Dirac moment",
                "For Higgs norm square x, the squared Dirac trace is four times x times the "
                + "weighted sum of squared Yukawa norms plus twice the squared Majorana norm."),
            Node("quartic-moment", "trace_dirac_four", "The quartic Dirac moment",
                "The quartic trace is four times x squared times the weighted sum of fourth "
                + "powers of the Yukawa norms, plus eight times x times the squared Majorana and "
                + "neutrino Yukawa norms, plus twice the fourth power of the Majorana norm."),
            Node("spectral-action", "potential_eq_spectral_action", "The radial spectral-action potential",
                "The quartic Dirac trace weighted by a minus the quadratic trace weighted by b "
                + "equals the radial potential evaluated at the squared Higgs norm."),
            Node("higgs-minimum", "higgs_minimum_iff", "The nonzero vacuum criterion",
                "For positive quartic weight and positive fourth Yukawa moment, the potential "
                + "on nonnegative norm squares has a positive minimizer exactly when b times the "
                + "second Yukawa moment exceeds twice a times the squared Majorana norm times "
                + "the squared neutrino Yukawa norm."),
            Node("higgs-minimum-massless", "higgs_minimum_massless", "The vacuum with zero Majorana mass",
                "When both action coefficients are positive and any Yukawa coupling is nonzero, "
                + "zero Majorana mass gives a positive minimizing Higgs norm square."))));

    private static DocumentBlock Node(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
