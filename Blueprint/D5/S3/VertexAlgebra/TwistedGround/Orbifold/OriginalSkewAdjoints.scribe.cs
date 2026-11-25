using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalSkewAdjointsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjoints of the Original Corrected Field and Translation",
        H("Adjoints of the Original Corrected Field and Translation"),
        Blocks(
            Entry("graded-adjoint", "actual_corrected_adjoint_of_grade",
                "Corrected-field transpose on a whole lattice grade",
                "For a positive definite lattice with unit Gram determinant, the transpose of coefficient e "
                + "on a homogeneous source of integer grade d is the sum of original corrected-field coefficients "
                + "at indices −e − 4d + 2j on states obtained by applying Sugawara mode one j times. The terms are weighted "
                + "by (−1) to the power d and inverse factorials. Nonnegative charge energy bounds each "
                + "monomial's oscillator weight by the grade, so Sugawara nilpotence gives a common cutoff "
                + "at the natural part of d. The source can have either theta parity."),
            Entry("fixed-grade-adjoint", "actual_corrected_grade_adjoint", "Transpose on the fixed grade",
                "Apply the whole-grade transpose to the underlying homogeneous state of the fixed grade."),
            Entry("translation-adjoint", "sourcePairing_translation", "Transpose of original translation",
                "Under the original source pairing, translation transposes to the inverse-Gram Sugawara "
                + "mode one. The all-state BPZ formula applied to the grade-two stress state has a single "
                + "surviving term because mode one kills that state."),
            Entry("translation-power-adjoint", "sourcePairing_fixedTranslation_pow",
                "Transpose of fixed translation powers",
                "Iterate the source-pairing identity to move every power of fixed translation to the "
                + "corresponding Sugawara power on the full source carrier."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
