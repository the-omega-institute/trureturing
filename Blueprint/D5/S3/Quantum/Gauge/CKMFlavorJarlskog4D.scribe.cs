using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class CKMFlavorJarlskog4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/ceccucci2024ckm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flavor parameter counts, Cabibbo rephasing, and the three-generation Jarlskog invariant.",
        H("Quark flavor mixing and the Jarlskog invariant"),
        Blocks(
            Paragraph(Text("Independent quark phases act on the rows and columns of a unitary flavor mixing matrix. "
                + "For two generations the action brings every matrix to a real rotation. "
                + "For three generations an imaginary quartet detects the phase contribution of the standard mixing matrix.")),
            Definition("unitary-count", "unitaryParamCount", "Unitary parameter count",
                "The count for N generations is the square of N."),
            Definition("angle-count", "orthogonalAngleCount", "Orthogonal angle count",
                "The angle count is half the product of N and N minus one."),
            Definition("relative-phases", "relativePhaseCount", "Relative phase count",
                "The two sets of quark phases share a common phase, giving twice N minus one relative phases."),
            Definition("physical-phases", "physicalPhaseCount", "Physical phase count",
                "The count is half the product of N minus one and N minus two, with subtraction in the natural numbers."),
            Entry("residual-square", "ckm_physical_parameter_square", "Physical parameter count",
                "For at least one generation, the unitary count minus the relative phase count equals the square of N minus one."),
            Entry("decomposition", "ckm_parameter_decomp", "Parameter count decomposition",
                "For at least one generation, the sum of the angle and physical phase counts equals the unitary count minus the relative phase count. Both expressions reduce to the square of N minus one."),
            Entry("minimum-generations", "cp_phase_pos_iff_three_generations", "Minimum generations for a physical phase",
                "The physical phase count is positive exactly when there are at least three generations."),
            Entry("small-generation-counts", "ckm_small_generation_counts", "Counts for one to three generations",
                "The angle and phase counts are zero and zero for one generation, one and zero for two, and three and one for three."),
            Definition("rephase", "rephase", "Independent row and column rephasing",
                "Multiply each entry by the phase of its row and the conjugate phase of its column."),
            Definition("quartet", "jarlskogQuartet", "Imaginary quartet",
                "Take one entry from each corner of a plaquette and conjugate the entries at the opposite cross corners. The quartet is the imaginary part of their product."),
            Entry("invariance", "jarlskogQuartet_rephase_invariant", "Quartet invariance under rephasing",
                "For any square complex matrix and any four indices, the phase of each row and column cancels with its conjugate in the quartet."),
            Entry("cabibbo", "u2_rephasing_to_real_rotation", "Two-generation reduction to a real rotation",
                "Every two-by-two unitary matrix admits diagonal row and column phase matrices and a real rotation angle. "
                + "The first row becomes nonnegative by removing the arguments of its entries, including zero entries. The determinant determines the remaining phase."),
            Entry("two-generation-zero", "u2_jarlskog_zero", "Two-generation quartets vanish",
                "For every two-by-two unitary matrix and all indices, the imaginary quartet is zero because the rephased real rotation has real plaquette products."),
            Definition("rotation-twenty-three", "rot23", "Rotation in the second and third directions",
                "The real rotation acts on the second and third directions and fixes the first."),
            Definition("rotation-thirteen", "rot13", "Complex rotation in the first and third directions",
                "The rotation fixes the second direction. The off-diagonal sine entries carry opposite phases, with the negative phase in the first row."),
            Definition("rotation-twelve", "rot12", "Rotation in the first and second directions",
                "The real rotation acts on the first and second directions and fixes the third."),
            Definition("standard-matrix", "ckmStandard", "Standard three-generation mixing matrix",
                "Multiply the second-third rotation, the complex first-third rotation, and the first-second rotation in that order."),
            Entry("unitarity", "ckmStandard_unitary", "Special unitarity of the standard matrix",
                "For every choice of the three angles and phase, the conjugate transpose times the matrix is the identity and the determinant equals one."),
            Definition("orientation", "leviSign", "Cyclic orientation sign",
                "An equal-index pair has sign zero. A positively oriented consecutive pair in the cyclic order of three indices has sign one and its reversal has sign minus one."),
            Entry("universal", "jarlskogQuartet_unitary_universal", "Universal signed quartet identity",
                "Every quartet of a three-by-three unitary matrix equals its first two rows and columns quartet times the row-pair and column-pair orientation signs. "
                + "The complex orthogonality sums close both sets of triangles, and the imaginary product is alternating."),
            Entry("standard-quartet", "jarlskog_ckmStandard_formula", "Standard quartet formula",
                "For the first two rows and columns, the quartet equals the product of the sines of the three angles and the phase, the cosines of the first-second and second-third angles, and the squared cosine of the first-third angle. The sign is positive with the stated plaquette convention."),
            Entry("vanishing", "jarlskog_zero_iff_no_cp", "Exact zero criterion",
                "The standard quartet vanishes exactly when the sine of either doubled real rotation angle, the sine or cosine of the first-third angle, or the sine of the phase vanishes."),
            Entry("sharp-bound", "jarlskog_sharp_upper_bound", "Sharp bound on the standard quartet",
                "The magnitude is at most one over six times the square root of three. Each real rotation contributes at most one half. "
                + "For the first-third rotation, putting x equal to squared sine factors the gap from four over twenty-seven as the square of x minus one third times four thirds minus x."),
            Entry("attainment", "jarlskog_bound_attained", "Angles attaining the bound",
                "The first-second and second-third angles equal pi over four, the first-third angle equals the arcsine of one over the square root of three, and the phase equals pi over two. The quartet attains the positive bound."),
            Entry("column-triangle", "unitarity_triangle_area_eq_half_jarlskog", "Column unitarity triangle area",
                "For any distinct column pair of a three-by-three unitary matrix, the three side products sum to zero. The oriented area from the first two products is minus half their quartet. Its absolute value is half the magnitude of the reference quartet."),
            Entry("row-triangle", "row_unitarity_triangle_area_eq_half_jarlskog", "Row unitarity triangle area",
                "For any distinct row pair of a three-by-three unitary matrix, the three side products sum to zero. The oriented area from the first two products is minus half their quartet. Its absolute value is half the magnitude of the reference quartet."))));

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Entry(id, declaration, title, statement, DescribeRole.Definition);

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
