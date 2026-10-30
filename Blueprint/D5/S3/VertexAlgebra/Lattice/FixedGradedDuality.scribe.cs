// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class FixedGradedDualityDocument : IScribeDocumentDefinition
{
    private static readonly string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.";

    private static DocumentBlock Theorem(string id, string name, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional fixed-energy graded duality on the original Carrier",
        H("Fixed-grade nondegeneracy and the algebraic restricted dual"),
        Blocks(
            Paragraph(Text("The construction uses the original Carrier D, its literal FixedCarrier D, and the existing grade D h. "
                + "The fixed grade is the comap of grade D h along the FixedCarrier inclusion. No alternate carrier and no live P1 pairing are introduced.")),
            Paragraph(Text("The ambient bilinear form B is an explicit parameter. The assumptions are ambient left and right nondegeneracy, "
                + "theta isometry, commutation of theta with the existing grade projection, and orthogonality of distinct grades. "
                + "The fixed-grade witness is plusPart D (gradeProjection h y): projection is recovered by the existing finite grade decomposition, "
                + "then theta averaging supplies fixed-space membership.")),
            Paragraph(Text("With the existing positive-Gram finite-grade supplier, every fixed grade is finite-dimensional. The proved restriction is "
                + "nondegenerate in both slots, so BilinForm.toDual gives the actual grade dual equivalence. The dependent direct sum of these "
                + "algebraic duals and its evaluation through the genuine fixed-energy decomposition are defined explicitly. For arbitrary fixed vectors x and y, including mixed finite energy support, evaluation of fixedRestrictedDualEquiv(x) at y equals B(x,y) on their original Carrier inclusions. The proof uses the existing internal direct sum: same-grade terms use the finite-grade pairing and all cross-grade terms vanish by the explicit orthogonality hypothesis.")),
            Paragraph(Text("Consequently the actual inverse represents every finitely supported grade functional f by the unique fixed vector x = fixedRestrictedDualEquiv.symm(f), with B(x,y) = fixedRestrictedDualEvaluation(f)(y) for every fixed y. This follows by applying the global identity to the inverse and using LinearEquiv.apply_symm_apply; it does not identify the restricted dual with the unrestricted algebraic dual of the full carrier.")),
            Paragraph(Text("This is a conditional algebraic supplier. It does not instantiate the live P1 pairing, prove module equivariance, all-source BPZ, "
                + "Hilbert or analytic CFT, fusion, full string theory, anomaly cancellation, or AdS-CFT.")),
            Definition("fixedgradedduality-fixedgrade", "FixedGrade", "The actual fixed grade, represented as grade D h comapped along the subtype inclusion into FixedCarrier D."),
            Definition("fixedgradedduality-fixedgradesubmodule", "fixedGradeSubmodule", "The fixed-grade submodule of FixedCarrier D."),
            Definition("fixedgradedduality-fixedgradetocarrier", "fixedGradeToCarrier", "The inclusion of a fixed grade into the original Carrier D."),
            Definition("fixedgradedduality-fixedgradeform", "fixedGradeForm", "The restriction of the explicit ambient bilinear form to the actual fixed grade."),
            Theorem("fixedgradedduality-fixedgradeform-apply", "fixedGradeForm_apply", "Evaluation of the restricted form is ambient B on the original Carrier inclusions."),
            Theorem("fixedgradedduality-fixedgradeprojection-mem", "fixedGradeProjection_mem", "A projected fixed vector remains in the actual fixed space under the explicit grade-commutation hypothesis."),
            Definition("fixedgradedduality-fixedgradeprojection", "fixedGradeProjection", "The actual projection from FixedCarrier D to its fixed grade h."),
            Theorem("fixedgradedduality-fixedgradeprojection-sum", "fixedGradeProjection_sum", "The finite stateEnergies support and existing sum_gradeProjections reconstruct every FixedCarrier vector."),
            Theorem("fixedgradedduality-fixedgrades-independent", "fixedGrades_independent", "Distinct actual fixed grades are internally independent by the existing grade independence."),
            Theorem("fixedgradedduality-fixedgrades-isup", "fixedGrades_iSup", "The actual fixed grades span FixedCarrier D using the existing finite decomposition and grade stability."),
            Definition("fixedgradedduality-fixedenergydecomposition", "fixedEnergyDecomposition", "The genuine linear equivalence between FixedCarrier D and the dependent direct sum of all actual fixed grades."),
            Theorem("fixedgradedduality-fixedgrade-finite", "fixedGrade_finiteDimensional", "Positive Gram supplies finite-dimensionality of every actual fixed grade."),
            Definition("fixedgradedduality-fixedgradewitness", "fixedGradeWitness", "The explicit projected and theta-averaged ambient witness in the actual fixed grade."),
            Theorem("fixedgradedduality-fixedgrade-dualequiv", "fixedGrade_dualEquiv", "Ambient nondegeneracy, theta isometry, grade stability and grade orthogonality imply genuine fixed-grade nondegeneracy and the finite-grade algebraic dual equivalence."),
            Definition("fixedgradedduality-fixedgrade-nondegenerate", "fixedGradeNondegenerate", "The selected nondegeneracy proof obtained from the explicit ambient witness construction."),
            Definition("fixedgradedduality-fixedgrade-dualequiv-selected", "fixedGradeDualEquiv", "The actual finite-grade equivalence to the full algebraic dual, built from the restricted form and its proved nondegeneracy."),
            Theorem("fixedgradedduality-fixedgrade-dualequiv-evaluation", "fixedGradeDualEquiv_evaluation", "The selected finite-grade dual equivalence evaluates to the restricted ambient form on every fixed grade."),
            Theorem("fixedgradedduality-fixedgrade-dualequiv-ambient-evaluation", "fixedGradeDualEquiv_ambient_evaluation", "The selected finite-grade dual equivalence evaluates to the original ambient bilinear form on the original Carrier inclusions."),
            Definition("fixedgradedduality-fixedrestricteddual", "FixedRestrictedDual", "The dependent direct sum of the full algebraic duals of all actual fixed grades."),
            Definition("fixedgradedduality-fixedrestricteddual-evaluation", "fixedRestrictedDualEvaluation", "Evaluation of an algebraic restricted-dual vector through the genuine fixed-energy decomposition."),
            Definition("fixedgradedduality-fixedrestricteddual-equiv", "fixedRestrictedDualEquiv", "The actual algebraic graded restricted-dual equivalence assembled from the finite-grade equivalences and the fixed-energy decomposition."),
            Theorem("fixedgradedduality-global-ambient-evaluation", "fixedRestrictedDualEquiv_ambient_evaluation", "For every pair of actual FixedCarrier vectors, evaluation of the constructed restricted-dual equivalence equals ambient B on the original Carrier inclusions, under ambient nondegeneracy, theta isometry, grade commutation, distinct-grade orthogonality and positive Gram."),
            Theorem("fixedgradedduality-fixedgrade-dual-evaluation", "fixedGrade_dual_evaluation", "The restricted form evaluates the inverse of toDual exactly as the given grade functional."))));
}
