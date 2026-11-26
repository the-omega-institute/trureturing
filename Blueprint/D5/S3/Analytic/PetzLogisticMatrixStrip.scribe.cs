using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzLogisticMatrixStripDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full logistic comparison for finite Frobenius matrix curves and their physical boundary pairs.",
        H("Matrix logistic boundary comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-full-logistic-of-boundary-cross"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.full_logistic_of_boundary_cross"),
                H("Exact energy with a prescribed cross term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take a bounded matrix curve continuous on the closed strip and holomorphic inside. Suppose two matrix residuals have the same trace cross term as the analytic boundary values. Assume the lower residual square is integrable against both weights and the upper residual square is integrable against the upper weight. The weighted boundary sum minus the logistic squared difference equals the lower residual square with the difference weight plus twice the analytic midline square integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-differentiable-exp-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.differentiable_exp_sum"),
                H("Finite spectral sums are entire"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite matrix-valued sum of complex exponentials with real frequencies is complex differentiable everywhere."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-norm-exp-sum-le"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.norm_exp_sum_le"),
                H("Uniform bound on finite spectral sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the absolute real part of the argument is at most a, the Frobenius norm is bounded by the sum of coefficient norms weighted by exp(a times the absolute frequency)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-sq-norm-mul-unitaries"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.sq_norm_mul_unitaries"),
                H("Preservation by two unitary multipliers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the left matrix has adjoint times itself equal to the identity and the right matrix has itself times its adjoint equal to the identity, multiplying on both sides preserves the Frobenius norm squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-residual"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.residual"),
                H("Analytic residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The analytic residual is R(1/2) minus S(z) O(z) R(1/2 − z)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-commonamplitude"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.commonAmplitude"),
                H("Common physical amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common amplitude is S(−it) R(1/2 + it)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-loweramplitude"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.lowerAmplitude"),
                H("Lower physical amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower amplitude is O(it) R(1/2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-upperamplitude"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.upperAmplitude"),
                H("Upper physical amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upper amplitude is S(1/2) O(1/2 + it)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-boundary-norms"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.boundary_norms"),
                H("Faithful boundary norms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For unital source and reference power laws compatible with adjoints, the same two unitary multipliers convert both analytic boundaries to their corresponding physical residuals. The two individual squares and the square of their difference agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petzlogisticmatrixstrip-supported-boundary-cross"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzLogisticMatrixStrip.supported_boundary_cross"),
                H("Cross term on singular input supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For multiplicative power laws compatible with adjoints and S(0) R(1/2) = R(1/2), the trace pairing of the two physical residuals equals the trace pairing of the analytic boundaries. The lower residual already has source right support and the upper residual has reference left support."))),
                DescribeRole.Theorem))));
}
