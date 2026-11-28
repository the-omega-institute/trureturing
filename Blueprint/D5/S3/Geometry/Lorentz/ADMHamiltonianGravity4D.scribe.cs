using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class ADMHamiltonianGravity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/arnowittdesermisner2008dynamics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ADM metric, Hamiltonian and time-symmetric conformal data.",
        H("The ADM metric, Hamiltonian and time-symmetric conformal data"),
        Blocks(
            Paragraph(Text("The lapse and shift describe a four-dimensional metric in a frame adapted to a spatial slice. In an orthonormal spatial frame the canonical momentum has one trace direction with negative kinetic form and five traceless directions with positive kinetic form. Time-symmetric isotropic data give explicit mass and area identities.")),
            Definition("adm-shift-matrix", "admShiftMatrix", "Shift matrix",
                "The unit lower triangular matrix adds the shift multiplied by the time component to the spatial components."),
            Definition("adm-spacetime-metric", "admMetric", "Spacetime metric",
                "The block form records the spatial metric, its pairings with the shift and the lapse term in the time entry."),
            Definition("adm-inverse-metric", "admInvMetric", "Inverse spacetime metric",
                "The spatial inverse is corrected by the shift outer product divided by the squared lapse. The time entry is minus the reciprocal squared lapse."),
            Entry("adm-metric-congruence", "admMetric_congruence_factorization", "Lapse and shift congruence",
                "The metric is the congruence of the block diagonal matrix with time entry equal to minus the lapse squared and spatial block equal to the spatial metric. The congruence uses the lower triangular shift matrix."),
            Entry("adm-metric-inverse", "admMetric_mul_inv", "Two-sided inverse",
                "A nonzero lapse and a two-sided spatial inverse give a two-sided inverse of the spacetime metric. Its mixed blocks are the shift components divided by the lapse squared."),
            Entry("adm-volume", "admMetric_det_and_volume", "Determinant and volume",
                "The determinant is minus the lapse squared times the spatial determinant. The square root of its negative is the positive lapse times the square root of the nonnegative spatial determinant."),
            Definition("adm-normal-vector", "nUp", "Normal vector components",
                "The contravariant components are the reciprocal lapse and the negative shift divided by the lapse."),
            Definition("adm-spatial-basis", "eSpatial", "Spatial coordinate basis",
                "A spatial coordinate vector has zero time component and one selected spatial component equal to one."),
            Entry("adm-normal", "adm_unit_timelike_normal", "Normal to the spatial slice",
                "For nonzero lapse the normal has time component equal to the reciprocal lapse and spatial components equal to the negative shift divided by the lapse. Lowering its index gives a covector with time component equal to the negative lapse and vanishing spatial components. Its squared length is minus one and its pairing with every spatial basis vector vanishes."),
            Entry("adm-signature", "adm_lorentzian_signature", "Lorentzian signature",
                "For positive lapse and symmetric positive definite spatial metric the quadratic form is the shifted spatial quadratic form minus the square of the lapse times the time component. Symmetry, negativity on the normal and positivity on the full spatial hyperplane determine the signature."),
            Definition("adm-momentum-map", "admMomentum", "Canonical momentum",
                "Subtract the curvature trace times the identity and multiply by the volume factor."),
            Definition("adm-inverse-momentum-map", "admExtrinsicFromMomentum", "Extrinsic curvature from momentum",
                "Subtract half the momentum trace times the identity and divide by the volume factor."),
            Definition("adm-kinetic-form", "dewittKinetic", "DeWitt kinetic form",
                "Take the trace of the momentum square and subtract half the square of its trace."),
            Entry("adm-legendre", "adm_legendre_transform_involution", "Momentum and extrinsic curvature",
                "In three spatial dimensions the forward and inverse trace-adjusted maps are mutual inverses at nonzero volume factor. Taking the trace of the momentum gives minus twice the volume factor times the curvature trace. Substitution into the quadratic kinetic form gives the inverse square of the volume factor and the momentum trace coefficient one half."),
            Entry("adm-dewitt", "dewitt_supermetric_lorentzian_signature", "Conformal and shear directions",
                "The trace part contributes minus one sixth of the squared trace. The traceless part contributes the trace of its square, strictly positive for nonzero symmetric shear. The projection remains symmetric. Two diagonal and three off-diagonal entries uniquely parametrize that shear. A nonzero scalar matrix has kinetic value minus three halves times its scalar coefficient squared."),
            Entry("adm-friedmann", "adm_hamiltonian_constraint_reproduces_friedmann", "Friedmann constraint",
                "At positive scale factor, raising one index of the extrinsic curvature gives the Hubble rate times the identity. The trace combination reduces to minus six times the Hubble rate squared. With spatial curvature six times the curvature parameter divided by the scale factor squared, the Hamiltonian constraint is equivalent to the first Friedmann equation."),
            Definition("adm-radial-laplacian", "radialLaplacian", "Radial Laplacian",
                "Add the second radial derivative to twice the first radial derivative divided by radius."),
            Definition("adm-conformal-curvature", "conformalScalarCurvature", "Conformal scalar curvature",
                "Multiply the radial Laplacian by minus eight times the inverse fifth power of the conformal factor."),
            Definition("adm-isotropic-schwarzschild", "schwPsi", "Schwarzschild conformal factor",
                "Add one to the mass divided by twice the isotropic radius."),
            Entry("adm-lichnerowicz", "lichnerowicz_radial_harmonic_vanishing", "The isotropic vacuum constraint",
                "On the positive radial half-line, twice differentiating the Schwarzschild conformal factor gives the opposite of twice its first derivative divided by radius. The radial Laplacian and the modeled conformal scalar curvature both vanish."),
            Definition("adm-areal-radius", "isotropicArealRadius", "Areal radius",
                "Multiply the isotropic radius by the square of the conformal factor."),
            Definition("adm-isotropic-inversion", "isotropicInversion", "Isotropic radial inversion",
                "Divide the squared mass by four times the isotropic radius."),
            Entry("adm-inversion", "isotropic_schwarzschild_throat_and_inversion_isometry", "Isotropic inversion and the throat",
                "For positive mass and radius, inversion by one quarter of the squared mass preserves the areal radius and pulls back the radial metric factor. The map is its own inverse and exchanges the intervals on either side of the throat. The areal radius has unique minimum twice the mass at isotropic radius equal to half the mass. This matches the horizon radius in the Kruskal bridge."),
            Definition("adm-conformal-flux", "conformalADMMass", "Conformal surface flux",
                "Multiply the first radial derivative by minus twice the square of the radius and the cube of the conformal factor."),
            Definition("adm-komar-mass", "komarSchwarzschildMass", "Komar mass expression",
                "Multiply the radial flux density by the sphere area and divide by four pi."),
            Entry("adm-mass", "schwarzschild_adm_mass_limit_and_komar_invariance", "Schwarzschild surface masses",
                "The finite-radius conformal flux is the mass times the cube of the conformal factor and converges to the mass at infinity. The Komar surface expression equals the mass at every positive areal radius."),
            Definition("adm-bl-conformal-factor", "blPsi", "Brill-Lindquist conformal factor",
                "Add one to the sum of the mass parameters divided by twice the distance to their respective centers."),
            Definition("adm-bl-outer-mass", "blADMMass", "Brill-Lindquist outer mass",
                "Sum the mass parameters of all centers."),
            Definition("adm-bl-inner-mass", "blBareMass", "Brill-Lindquist inner mass",
                "Multiply the selected mass parameter by the conformal factor from all the other centers evaluated at the selected center."),
            Entry("adm-punctures", "brill_lindquist_harmonic_positive_mass_and_binding_energy", "Brill-Lindquist flux and binding",
                "The conformal factor is harmonic off the punctures. Its normalized radial flux tends on every unit ray to the sum of the mass parameters, which is positive for nonempty data with positive masses. The binding energy is minus one half of the sum over ordered distinct pairs of their mass product divided by distance. It is strictly negative if there are at least two centers, the centers are pairwise distinct and all masses are positive."),
            Entry("adm-penrose", "riemannian_penrose_inequality_schwarzschild_saturation", "Schwarzschild equality case",
                "For positive mass, the throat area is sixteen pi times the square of the mass, and the square root of the area divided by sixteen pi equals the mass. At zero Kruskal time the throat relation forces the spatial Kruskal coordinate to vanish."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Definition);
}
