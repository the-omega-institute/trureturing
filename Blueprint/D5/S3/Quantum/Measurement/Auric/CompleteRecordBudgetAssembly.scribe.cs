using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CompleteRecordBudgetAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exhaustive certificate cases and their physical transfer",
        H("The exhaustive certificate cases and their physical transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-spectral-budget-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.exists_spectral_budget_certificate"),
                H("Existence in the smaller dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("When twice the working dimension is at most total capacity, nonnegative traces bounded by their capacities and summing to the dimension admit a certificate. The cases are zero dimension, excess deficits, a saturated trace, a zero trace, and the strict direct or complementary equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-budget-certificate-maximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.spectral_budget_certificate_maximum"),
                H("Every certificate gives a greatest spectral value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For admissible trace data, any certificate supplies the greatest feasible spectral score. Saturated and zero faces use the common binary optima of the two objectives, and strict certificates use the original-label optima."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-budget-of-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.complete_budget_of_geometry"),
                H("Physical attainment via the exact range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The range equality turns the spectral optimum into a greatest pinching gain divided by the input rank. The coherent record identities give the mutual information and conditional entropy extrema. A feasible law has an attaining input, while any admissible input supplies positive effects whose trace and rank bounds imply feasibility."))),
                DescribeRole.Theorem))));
}
