using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFunctionMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Paired Function Metric", H("Actual Paired Function Metric"),
        Blocks(
            Paragraph(Text("Put mu0=log(2)^2/4, gamma=pi/4 and kappa0=mu0/(1+gamma^2+mu0). An exact two-by-two sum of squares proves the pointwise function estimate using the actual mean lower bound.")),
            Paragraph(Text("For every c>=3 and arbitrary complex polynomials A,B, kappa0 times the integral on [-1,1] of norm(A(t))^2+norm(B(t))^2 is at most pairedEnergy(c,A,B). Reflection joins the two halves of the integral. This is an integral function metric estimate; it uses no monomial/Hilbert coefficient conversion and has no nonzero-vector premise.")),
            Describe.Lean(DescribeId.Create("mu0"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFunctionMetric.mu0"),
                H("mu0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lean defining declaration: def mu0 : ℝ := (Real.log (2:ℝ))^2/4."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFunctionMetric.gamma"),
                H("gamma"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lean defining declaration: def gamma : ℝ := Real.pi/4."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kappa0"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFunctionMetric.kappa0"),
                H("kappa0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lean defining declaration: def kappa0 : ℝ := mu0/(1+gamma^2+mu0)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-paired-function-metric"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFunctionMetric.actual_paired_function_metric"),
                H("actual paired function metric"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean telescope and conclusion: theorem actual_paired_function_metric {c : ℕ} (hc : 3 ≤ c) (A B : ℂ[X]) : kappa0*(∫ t in (-1:ℝ)..1, (‖value A t‖^2+‖value B t‖^2)) ≤ pairedEnergy c A B."))),
                DescribeRole.Theorem))));
}
