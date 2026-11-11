using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;
internal sealed class ActualTwoFourCutoffCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualTwoFourCutoffCurvature", H("SOURCE ONLY candidate"),
        Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Full mathematical candidate bodies exist. No parser, build, Lean kernel, axiom closure, Scribe, lawful registration, variation, binding, official or RH acceptance is asserted. Ordinary Pro input is fallible. The exact original-record/arbitrary-original-price/energy endgoals belong to other owners.")),
            Describe.Lean(
                DescribeId.Create("actual-two-four-normalized-gain-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds"),
                H("normalized_gain_bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem normalized_gain_bounds {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 2 ≤ u) :     1 - 1 / u ≤ gain j u * u ^ j ∧ gain j u * u ^ j ≤ 1 ∧       -2 / u ≤ log (gain j u * u ^ j) ∧ log (gain j u * u ^ j) ≤ 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-actual-two-four-curvature-tendsto"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto"),
                H("actual_two_four_curvature_tendsto"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem actual_two_four_curvature_tendsto :     Tendsto (fun X : ℝ => log X ^ 2 *       ((4 * log (cutoff 4 (referencePrice X)) - log X) -         2 * (2 * log (cutoff 2 (referencePrice X)) - log X)))       atTop (𝓝 (log (2 : ℝ) ^ 2))"))),
                DescribeRole.Theorem)
        )));
}
