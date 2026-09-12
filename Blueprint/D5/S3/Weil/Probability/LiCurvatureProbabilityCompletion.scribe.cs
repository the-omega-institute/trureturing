using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class LiCurvatureProbabilityCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.",
        H("LiCurvatureProbabilityCompletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalized-curvature-reconstruction"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_reconstruction"), H("One measure reconstructs the entire original sequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All normalized curvature matrices determine a unique probability measure. Existing second-difference uniqueness identifies every original coefficient with the existing geometric-polynomial energy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-curvature-forces-nonnegative"),
                DeclarationHandle.Create(Prefix + "normalized_curvature_forces_nonnegative"), H("Constructed curvature measure implies coefficient positivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonnegative first coefficient and the original recurrence yield positivity of every coefficient via the constructed measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("li-curvature-criterion-without-herglotz"),
                DeclarationHandle.Create(Prefix + "li_curvature_criterion_without_herglotz"), H("Remove the supplied Herglotz representation premise"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization is stated explicitly. The canonical arithmetic Li criterion and RH Fourier representation remain assumptions; the common probability measure no longer does."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("time-one-li-probability-implies-rh"),
                DeclarationHandle.Create(Prefix + "time_one_li_probability_implies_rh"), H("The reverse implication only needs the time-one law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moment modulus bound proves nonnegative coefficients for a supplied time-one law. This consumes an explicit arithmetic Li criterion and does not assert the law exists."))), DescribeRole.Theorem))));
}
