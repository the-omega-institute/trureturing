using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilProjectiveRoucheBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate mathematical source; compilation and admission are not claimed.",
        H("WeilProjectiveRoucheBudget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weilprojectiverouchebudget-finite-mesh-modulus-floor"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget.finite_mesh_modulus_floor"),
                H("A finite mesh with a certified variation bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coverage at radius h, sampled modulus floor m, and variation bounded by L times distance imply the boundary floor m-L*h. Both coverage and variation are required. Finite samples alone give no such floor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverouchebudget-variational-mesh-rouche-boundary"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget.variational_mesh_rouche_boundary"),
                H("Squared error budget for actual linear readouts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuous linear readout norm is bounded by K. A vector energy budget gap*norm(v-k)^2<=width and the strict inequality K^2*width<(m-L*h)^2*gap give the strict Rouche inequality everywhere on the covered boundary. This avoids numerical square roots. Readout norm, mesh coverage, sampled modulus, and variation remain explicit certified inputs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverouchebudget-rectangle-zero-count-eq-of-projective-rayleigh"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget.rectangle_zero_count_eq_of_projective_rayleigh"),
                H("From the operator-domain enclosure to analytic multiplicities"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compose projective_rayleigh_enclosure with the finite mesh transport and the existing rectangle_zero_count_eq_of_norm_sub_lt. The actual projectively normalized eigenvector readout and candidate readout occur in the conclusion. Analyticity and exact finite zero sets are retained exactly as required by the existing zero-count API. No claim is made that Fourier/L2 representation, mesh bounds, all-scale control, Xi convergence, or RH have already been proved."))),
                DescribeRole.Theorem))));
}
