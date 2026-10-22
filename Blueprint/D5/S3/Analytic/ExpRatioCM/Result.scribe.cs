using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient extraction and the low-index classification of exponential derivative ratios.",
        H("Failure and classification from the extracted coefficient"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-cm-failure-family"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le"),
                H("Indices at least three"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an index at least three, the second quotient coefficient is 2 times 3 to the index minus 4 to the index, hence negative. The extraction contradiction excludes complete monotonicity for either ratio family once the corresponding limits are supplied."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-classification"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.classification_of_limits"),
                H("Classification from positive cases and limits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combining complete monotonicity of the low-index coefficient cases with the failure family gives the exact index classification for each ratio family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-result-of-limits"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.result_of_limits"),
                H("Refutation from the extracted limits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal conjecture is contradicted by the failure at index three once the two extracted limits and the positive low-index cases have been established."))),
                DescribeRole.Theorem))));
}
