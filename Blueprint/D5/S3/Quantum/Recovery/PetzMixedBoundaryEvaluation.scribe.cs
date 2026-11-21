using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzMixedBoundaryEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logistic evaluation coefficient counts distinct levels of the two output spectra.",
        H("Logistic evaluation in a mixed output eigenbasis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petzmixedboundaryevaluation-levelcount"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.levelCount"),
                H("Distinct spectral levels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real family on a finite carrier, count the elements of its image."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzmixedboundaryevaluation-mixedboundary"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary"),
                H("Mixed boundary curve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The curve uses the reference basis on the left and the source basis on the right. The first product has imaginary output powers followed by a square coefficient matrix. The second starts with another square coefficient matrix and uses the displaced output powers. A rectangular connector joins the eigenbases. In the physical application the square matrices represent the source and reference square roots."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzmixedboundaryevaluation-mixedboundary-evaluation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary_evaluation"),
                H("Evaluation with distinct levels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full logistic density times the squared Frobenius norm of the mixed curve is integrable. Its integral times the sum of the distinct level counts minus one bounds the squared norm at time zero. In each entry the two frequency lists have the frequency log(p_j) − log(q_i) in common."))),
                DescribeRole.Theorem))));
}
