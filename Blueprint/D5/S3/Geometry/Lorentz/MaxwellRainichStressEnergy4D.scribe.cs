using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class MaxwellRainichStressEnergy4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.";
    private static readonly LibraryNoteRef Rainich =
        LibraryNoteRef.Create("D5/L/Observer/rainich1925electrodynamics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-dimensional electromagnetic invariants, the Maxwell stress tensor and its Rainich square.",
        H("Maxwell stress, electromagnetic invariants and causal energy flux"),
        Blocks(
            Paragraph(Text("The covariant electromagnetic tensor uses signature (+,−,−,−). Its time-space row contains the electric vector and its spatial block is the matrix of cross product by the magnetic vector. The Hodge dual exchanges the electric and magnetic vectors with signs minus and plus, respectively.")),
            Entry("field-antisymmetry", "fieldTensor_antisym", "Antisymmetry of the field tensor",
                "Transposing the covariant field tensor negates it for every pair of electric and magnetic vectors."),
            Entry("dual-square", "dualFieldTensor_sq", "Square of Hodge duality",
                "Taking the Hodge dual of the pair with electric vector minus the original magnetic vector and magnetic vector the original electric vector negates the original field tensor."),
            Entry("field-coordinates", "fieldTensor_bijective", "Electric and magnetic coordinates",
                "The map from pairs of real three-vectors to antisymmetric real four-by-four matrices is bijective."),
            Entry("scalar-contractions", "maxwell_invariants_explicit", "Scalar and oriented contractions",
                "Half the contraction of the field tensor with its raised tensor is the magnetic squared length minus the electric squared length. One quarter of the contraction with the raised dual is the electric and magnetic dot product."),
            Entry("field-determinant", "fieldTensor_det", "Field determinant",
                "The determinant of the covariant field tensor is the square of the electric and magnetic dot product."),
            Entry("lorentz-invariants", "maxwell_invariants_lorentz_invariant", "Lorentz invariance of both contractions",
                "For a metric-preserving matrix with determinant one, the congruence by that matrix preserves both contractions after recovering the transformed electric and magnetic vectors. In coordinates it preserves the difference of squared lengths and the signed dot product."),
            Entry("stress-symmetry", "maxwell_stress_symmetric", "Symmetric covariant stress",
                "Lowering the first index of the mixed Maxwell stress gives a symmetric matrix."),
            Entry("stress-trace", "maxwell_stress_traceless", "Vanishing mixed trace",
                "The mixed Maxwell stress has trace zero for every electromagnetic field."),
            Entry("energy-poynting", "maxwell_energy_and_poynting", "Energy, Poynting vector and spatial stress",
                "The mixed time-time entry is half the sum of the squared electric and magnetic lengths. Its time-space row is minus the Poynting vector, which is the cross product of the electric and magnetic vectors in that order. The fully raised time-space row is the Poynting vector, and the fully raised spatial block is the energy density times the identity minus the electric and magnetic outer products."),
            Entry("stress-covariance", "maxwell_stress_lorentz_covariant", "Lorentz covariance of stress",
                "For every metric-preserving matrix, the covariant stress of the transformed field is the congruence of the original covariant stress by that matrix."),
            Entry("duality-invariance", "maxwell_duality_rotation_invariant", "Invariance under duality rotation",
                "For every real angle, replace the electric vector by cosine times electric plus sine times magnetic, and the magnetic vector by minus sine times electric plus cosine times magnetic. Both the mixed and covariant stress remain invariant."),
            Entry("poynting-bound", "poynting_le_energy_density", "Poynting bound and algebraically null fields",
                "The length of the Poynting vector is at most the energy density. Equality holds exactly when the electric and magnetic squared lengths agree and their dot product vanishes."),
            Entry("rainich-square", "maxwell_rainich_square_identity", "Rainich square identity",
                "The mixed stress squares to a scalar multiple of the identity. The scalar is the sum of one quarter of the squared difference of the magnetic and electric squared lengths and the squared electric and magnetic dot product.", Rainich),
            Entry("null-stress-square", "maxwell_stress_nilpotent_iff_null", "Vanishing stress square",
                "The mixed stress squares to zero exactly when the electric and magnetic squared lengths agree and their dot product vanishes."),
            Entry("dominant-energy", "maxwell_dominant_energy_condition", "Causal energy flux and nonnegative energy",
                "For any observer vector with nonnegative time coordinate and Minkowski squared norm, its quadratic pairing with the covariant stress is nonnegative. The flux obtained by applying the mixed stress has nonnegative time coordinate. Its Minkowski squared norm is the observer's Minkowski squared norm times the Rainich coefficient and is nonnegative."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(acknowledgements),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
