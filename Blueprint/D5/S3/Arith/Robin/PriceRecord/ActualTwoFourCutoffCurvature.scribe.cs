using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;
internal sealed class ActualTwoFourCutoffCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualTwoFourCutoffCurvature", H("D5 source compiled; RegUNVALIDATED"),
        Blocks(Paragraph(Text("The statements below concern the finite floor mesh and actual two/four cutoff curvature. They do not establish the complete paid-prefix repair or Robin inequality. RegUNVALIDATED: lawful registration, variation and source binding remain unfinished.")),
            Paragraph(Text("The reusable offset is d(j,X)=j log(cutoff j(referencePrice X))-log X. The normalized gain error eta(j,X) is log(gain j(cutoff j(referencePrice X)) * cutoff j(referencePrice X)^j). The transform is F(L,a)=a+log(1+a/L). Its secant theorem requires L>0 and nonnegative endpoints. The normalized gain error tends to zero after multiplication by any fixed natural power of log X, using eventual log X>=0. The original second-order curvature theorem consumes the n=2 specialization; the mixed fourth-order actual-root theorem consumes n=4.")),
            Describe.Lean(
                DescribeId.Create("actual-two-four-normalized-gain-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds"),
                H("normalized_gain_bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact full statement: theorem normalized_gain_bounds {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 2 ≤ u) :     1 - 1 / u ≤ gain j u * u ^ j ∧ gain j u * u ^ j ≤ 1 ∧       -2 / u ≤ log (gain j u * u ^ j) ∧ log (gain j u * u ^ j) ≤ 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-actual-two-four-curvature-tendsto"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto"),
                H("actual_two_four_curvature_tendsto"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact full statement: theorem actual_two_four_curvature_tendsto :     Tendsto (fun X : ℝ => log X ^ 2 *       ((4 * log (cutoff 4 (referencePrice X)) - log X) -         2 * (2 * log (cutoff 2 (referencePrice X)) - log X)))       atTop (𝓝 (log (2 : ℝ) ^ 2))"))),
                DescribeRole.Theorem) ,
            Describe.Lean(DescribeId.Create("actual-two-four-actual-root-equation"), DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_root_equation"), H("actual_root_equation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact full statement: theorem actual_root_equation{j : ℕ} (hj : 2 ≤ j) : ∀ᶠ X : ℝ in atTop, 0 < d j X ∧ 2 < cutoff j (referencePrice X) ∧ F (log X) (d j X) = log (j : ℝ) + η j X"))), DescribeRole.Theorem) ,
            Describe.Lean(DescribeId.Create("actual-two-four-scaled-root-error"), DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.scaled_root_error"), H("scaled_root_error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact full statement: theorem scaled_root_error{j : ℕ} (hj : 2 ≤ j) (n : ℕ) : Tendsto (fun X : ℝ => log X ^ n * η j X) atTop (𝓝 0)"))), DescribeRole.Theorem) ,
            Describe.Lean(DescribeId.Create("actual-two-four-f-secant"), DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.F_secant"), H("F_secant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Exact full statement: theorem F_secant{L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) : ∃ q : ℝ, 1 ≤ q ∧ q ≤ 1 + 1 / L ∧ F L b - F L a = (b - a) * q"))), DescribeRole.Theorem)
        )));
}
