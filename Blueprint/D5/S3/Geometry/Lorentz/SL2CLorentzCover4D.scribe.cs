using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class SL2CLorentzCover4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/tong2007quantumfieldtheory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pauli conjugation defines a surjective homomorphism onto the proper orthochronous Lorentz matrices with kernel ±I.",
        H("The spinor double cover of the proper orthochronous Lorentz group"),
        Blocks(
            Paragraph(Text(
                "Use the metric diag(1, −1, −1, −1). A four-vector specifies a Hermitian Pauli matrix, "
                + "and the determinant of that matrix is the Minkowski squared norm. Determinant-one "
                + "complex matrices act by conjugation with the adjoint. Euler rotations and an axial "
                + "boost produce a spinor lift of each proper orthochronous Lorentz matrix.")),
            Definition("real-coordinates", "V4", "Real four-vectors",
                "Use four real coordinates in time, x, y, z order."),
            Definition("complex-matrices", "H2", "Complex two-by-two matrices",
                "Use two rows and two columns indexed from zero."),
            Definition("special-linear", "SL2C", "The spinor group",
                "Take the group of complex two-by-two matrices with determinant one."),
            Definition("metric", "eta", "The Minkowski metric",
                "The four diagonal entries are one, minus one, minus one and minus one."),
            Definition("quadratic-form", "minkowskiNormSq", "Minkowski quadratic form",
                "Subtract the sum of the three squares of the spatial coordinates from the square of the time coordinate."),
            Definition("pauli-embedding", "pauliHerm", "Hermitian Pauli coordinates",
                "For coordinates (t, x, y, z), use diagonal entries t + z and t − z and off-diagonal entries x − iy and x + iy."),
            Definition("pauli-inverse", "minkowski_from_pauliHerm", "Minkowski coordinates",
                "Use half the real diagonal sum, the real and negated imaginary parts of the upper-right entry, and half the real diagonal difference."),
            Entry("pauli-hermitian", "pauliHerm_isHermitian", "Hermitian image",
                "The Pauli matrix of every real four-vector equals its conjugate transpose."),
            Entry("vector-round-trip", "pauliHerm_minkowski_inverse", "Recovery of the four-vector",
                "Taking Minkowski coordinates of the Pauli matrix recovers the original real four-vector."),
            Entry("matrix-round-trip", "minkowski_pauliHerm_inverse", "Recovery of the Hermitian matrix",
                "For each Hermitian two-by-two complex matrix, taking Minkowski coordinates and forming the Pauli matrix recovers that matrix."),
            Entry("pauli-determinant", "pauliHerm_det", "Minkowski squared norm",
                "The determinant of the Pauli matrix equals t² − x² − y² − z² embedded into the complex numbers."),
            Entry("pauli-trace", "pauliHerm_trace", "Time coordinate",
                "The trace of the Pauli matrix equals twice the time coordinate embedded into the complex numbers."),
            Definition("minkowski-action", "lorentzVec", "Action on four-vectors",
                "Conjugate the Pauli matrix by the spinor matrix and its adjoint, then take Minkowski coordinates."),
            Definition("lorentz-matrix", "lorentzOfSL2C", "Spinor-to-Lorentz map",
                "The columns are the actions of spinor conjugation on the four coordinate basis vectors."),
            Entry("pauli-covariance", "pauliHerm_lorentzVec", "Pauli covariance",
                "Encoding the transformed four-vector gives the original Pauli matrix multiplied on the left by the spinor matrix and on the right by its adjoint."),
            Entry("matrix-action", "lorentzOfSL2C_mulVec", "Matrix action",
                "Multiplication by the matrix of basis images agrees with spinor conjugation on every four-vector."),
            Entry("identity", "lorentzOfSL2C_one", "Identity",
                "The identity spinor matrix maps to the identity Lorentz matrix."),
            Entry("multiplication", "lorentzOfSL2C_mul", "Multiplication",
                "The image of a product of spinor matrices is the product of their images in the same order."),
            Entry("norm-preserved", "lorentzOfSL2C_preserves_norm", "Minkowski norm preservation",
                "The determinant-one and Hermitian conjugation identities give preservation of the Minkowski squared norm."),
            Entry("metric-preserved", "lorentzOfSL2C_preserves_minkowski", "Metric preservation",
                "Polarization of the squared norm gives Lᵀ η L = η for each spinor image L."),
            Entry("future-preserved", "lorentzOfSL2C_orthochronous", "Time orientation",
                "The time-time coordinate is at least one. It is half the sum of the four squared entry norms and dominates the norm of the spinor determinant."),
            Entry("kernel", "lorentzOfSL2C_ker_iff", "Exact two-element kernel",
                "The identity has preimages I and −I. Fixing the time basis matrix makes the spinor matrix unitary. Fixing the diagonal and off-diagonal Pauli matrices forces it to be scalar, and the square of the scalar is one."),
            Entry("fibers", "lorentzOfSL2C_eq_iff", "Exact fibers",
                "Two spinor matrices have the same image exactly when one is the other or its negative."),
            Definition("proper-orthochronous", "IsProperOrthochronous", "Proper orthochronous matrices",
                "The matrix preserves the Minkowski metric, has determinant one, and has a strictly positive time-time entry."),
            Entry("z-rotation", "lorentzOfSL2C_rotZ", "Spinor image of a z rotation",
                "The image fixes time and z. On x and y, the rows are (cos θ, −sin θ) and (sin θ, cos θ)."),
            Entry("y-rotation", "lorentzOfSL2C_rotY", "Spinor image of a y rotation",
                "The image fixes time and y. On x and z, the rows are (cos φ, sin φ) and (−sin φ, cos φ)."),
            Entry("z-boost", "lorentzOfSL2C_boostZ", "Spinor image of a z boost",
                "The image fixes x and y. On time and z, the diagonal entries are cosh η and the off-diagonal entries are sinh η."),
            Entry("z-rotation-determinant", "lorentzOfSL2C_rotZ_det", "Determinant of a z rotation",
                "The spinor image of every z rotation has determinant one."),
            Entry("y-rotation-determinant", "lorentzOfSL2C_rotY_det", "Determinant of a y rotation",
                "The spinor image of every y rotation has determinant one."),
            Entry("z-boost-determinant", "lorentzOfSL2C_boostZ_det", "Determinant of a z boost",
                "The spinor image of every z boost has determinant one by cosh squared minus sinh squared."),
            Entry("spatial-lift", "so3_spinor_lift", "Lift of spatial rotations",
                "Every real three-by-three orthogonal matrix of determinant one is the spatial block of the Lorentz image of a unitary spinor matrix of determinant one."),
            Entry("gram-properties", "sl2c_gram_properties", "Hermitian Gram matrix of a spinor transformation",
                "The product of a determinant-one spinor matrix with its adjoint is positive definite, has determinant one, and has real trace at least two."),
            Entry("cartan-factorization", "sl2c_cartan_factorization", "Spinor Cartan factorization",
                "Every determinant-one spinor matrix is a product of two unitary determinant-one spinor matrices with a z boost between them."),
            Entry("proper-image", "lorentzOfSL2C_det_one", "Determinant one",
                "Every spinor image has determinant one. Rotations align the spatial part of the Hermitian matrix A Aᴴ, and an axial boost removes its two positive reciprocal eigenvalues. The resulting spinor is unitary, so the spinor factors into rotations and a boost."),
            Entry("future-proper-image", "lorentzOfSL2C_isProperOrthochronous", "Proper orthochronous image",
                "Every spinor image preserves the Minkowski metric, has determinant one, and has a positive time-time entry."),
            Entry("onto", "lorentzOfSL2C_surjective", "Constructive surjectivity",
                "For a proper orthochronous Lorentz matrix, rotate the spatial part of its time column onto the nonnegative z axis and remove it with a boost. The remaining matrix fixes the time vector and has a spatial rotation block. Lift the spatial rotation by Euler angles and undo the boost and the first rotation."),
            Definition("spinor-outer", "spinor_to_future_null", "Spinor outer product in Minkowski coordinates",
                "Form the Hermitian outer product of a two-component spinor with its adjoint and take Minkowski coordinates."),
            Entry("outer-recovery", "pauliHerm_spinor_outer", "Recovery of the outer product",
                "The Pauli matrix of the resulting vector has entries ψᵢ times the conjugate of ψⱼ."),
            Entry("null", "spinor_to_future_null_null", "Nullity",
                "The squared Minkowski norm of the spinor image is zero because the outer product has determinant zero."),
            Entry("nonnegative-time", "spinor_to_future_null_time_nonneg", "Nonnegative time coordinate",
                "The time coordinate of the spinor image is half the sum of the two squared spinor entry norms."),
            Entry("spinor-equivariance", "spinor_to_future_null_equivariant", "Spinor-to-null equivariance",
                "Transforming a spinor before taking its outer product gives the same Minkowski vector as acting on the original null vector by the associated Lorentz matrix."),
            Definition("mobius", "sl2c_celestial_mobius", "Celestial Möbius transformation",
                "For the matrix with rows (a, b) and (c, d), the affine transformation is z ↦ (az + b)/(cz + d)."),
            Entry("mobius-equivariance", "sl2c_celestial_mobius_equivariant", "Affine celestial equivariance",
                "When the second coordinates of both the original and transformed spinor are nonzero, their coordinate ratios are related by the corresponding Möbius transformation."))));

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Entry(id, declaration, title, statement, DescribeRole.Definition);

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
