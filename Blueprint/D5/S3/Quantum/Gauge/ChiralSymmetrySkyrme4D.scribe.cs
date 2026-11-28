using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class ChiralSymmetrySkyrme4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.";
    private static readonly LibraryNoteRef Gmor =
        LibraryNoteRef.Create("D5/L/LieTheory/gellmannoakesrenner1968chiral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-flavor chiral orbit, the tree-level pion mass and anomaly factor, and Skyrme energy bounds.",
        H("Two-flavor chiral symmetry, pion masses and Skyrme energy"),
        Blocks(
            Paragraph(Text("The left and right SU(2) factors act on the chiral field by multiplication on the left and inverse multiplication on the right. The chiral potential is the real trace of the diagonal quark mass matrix times the field, weighted by minus the mass parameter times the squared decay constant.")),
            Entry("vacuum-stabilizer", "chiral_vacuum_stabilizer_iff", "Diagonal vacuum stabilizer",
                "The pair of left and right group elements fixes the identity field exactly when its two entries are equal."),
            Entry("vacuum-orbit", "chiral_orbit_transitive", "Chiral vacuum orbit",
                "Every determinant-one unitary two-by-two matrix is the image of the identity under some left and right group elements."),
            Describe.Lean(DescribeId.Create("vacuum-cosets"), DeclarationHandle.Create(Prefix + "chiralCosetEquiv"),
                H("Cosets of the diagonal subgroup"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence from left cosets of the diagonal subgroup sends the coset of a left and right pair to its action on the identity. The inverse sends a field to the coset of the pair with that field on the left and the identity on the right."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-sphere"), DeclarationHandle.Create(Prefix + "su2SphereCoordinates"),
                H("Three-sphere coordinates for SU(2)"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real part of the upper-left entry, the imaginary and real parts of the upper-right entry, and the imaginary part of the upper-left entry give the four real coordinates in that order. The map and its continuous inverse identify SU(2) with the unit sphere in real four-space."))), DescribeRole.Definition),
            Entry("field-exponential", "chiralField_eq_exp", "Matrix exponential of the pion field",
                "For every real decay parameter and pion triple, the closed field formula equals the matrix exponential of the Pauli matrix of the triple scaled by the imaginary unit divided by the decay parameter. At zero decay parameter both sides are the identity under totalized division."),
            Entry("field-unitarity", "chiralField_mem_su2", "Pion field in SU(2)",
                "At nonzero decay constant the cosine term and the sinc-weighted Pauli term give a unitary matrix of determinant one for every real pion triple. The sinc function is the sine divided by its argument, with value one at zero."),
            Entry("field-origin", "chiralField_zero", "Pion field at the origin",
                "The zero pion triple gives the identity matrix."),
            Entry("kinetic-normalization", "chiral_kinetic_quadratic_normalization", "Canonical quadratic kinetic normalization",
                "For positive decay constant and any pion direction, the directional field curve is differentiable at zero. Its derivative is the Pauli matrix of the direction times the imaginary unit divided by the decay constant. The real trace of its Hermitian adjoint times itself, weighted by one quarter of the squared decay constant, is half the squared Euclidean length of the direction."),
            Entry("potential-minimum", "chiralPotential_global_min_at_one", "Unique minimum of the mass potential",
                "For positive mass parameter, decay constant and both quark masses, the chiral potential over SU(2) is minimized at the identity. Equality with the minimum holds exactly at the identity matrix."),
            Entry("pion-hessian", "gmor_exact_hessian", "Directional Hessian of the pion potential",
                "At positive decay constant the second derivative at zero along any pion line is the mass parameter times the quark mass sum times the squared Euclidean length of the direction.", Gmor),
            Entry("gmor-mass", "gmor_pion_mass_relation", "Common pion mass and chiral limit",
                "At positive decay constant the common squared mass is the mass parameter times the quark mass sum. Multiplying it by the squared decay constant gives the quark mass sum times the condensate parameter. The three coordinate directions have this same curvature. With fixed mass parameter, the squared mass tends to zero as the quark mass sum tends to zero.", Gmor),
            Entry("anomaly-free-charges", "abj_anomaly_free_general_Nc", "Cancellation of the color factor",
                "For each nonzero real color parameter, divide its sum with one by twice the color parameter to obtain the up charge. Divide one minus the color parameter by the same denominator to obtain the down charge. These charges yield anomaly factor one."),
            Entry("fixed-charge-test", "abj_fixed_charges_color_test", "Color dependence at fixed charges",
                "At fixed charges two thirds and minus one third the anomaly factor is the color parameter divided by three. The factor is one at three colors. For positive decay constant the normalized two-photon width at three colors is nine times its value at one color."),
            Entry("faddeev-bound", "faddeev_bogomolny_skyrme_bound", "Pointwise Skyrme energy bound",
                "For every real strain triple, the quadratic energy, obtained by summing strain squares, plus the quartic energy, obtained by summing products of distinct strain squares over unordered pairs, is at least six times the absolute product of the three strains."),
            Entry("faddeev-saturation", "faddeev_bogomolny_saturation_iff", "Equality in the pointwise bound",
                "Equality holds exactly when all three strains vanish or all three have absolute value one."),
            Entry("pure-sigma-scaling", "derrick_no_pure_sigma_soliton", "Pure sigma energy under spatial scaling",
                "With positive quadratic energy and zero quartic energy, the energy is strictly decreasing on positive scales, tends to zero at positive infinity, and has no minimum on that interval."),
            Entry("skyrme-virial", "derrick_skyrme_virial_minimum", "Unique Skyrme scaling minimum",
                "When both energy coefficients are positive, the reciprocal-scale quadratic term and the linear-scale quartic term coincide at the square root of their coefficient ratio. This positive scale is the unique strict global minimizer, with energy twice the square root of the coefficient product."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(acknowledgements),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
