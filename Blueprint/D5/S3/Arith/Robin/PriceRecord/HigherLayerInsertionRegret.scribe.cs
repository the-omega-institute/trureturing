using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLayerInsertionRegretDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HigherLayerInsertionRegret",
        H("D5 source compiled; RegUNVALIDATED"),
        Blocks(
            Paragraph(Text("The D5 source target has a current scoped Lean build. The retained Reg source compiles; the escape audit remains incomplete for lawful registration, source occurrence binding and official/RH acceptance; no literature novelty or consensus claim is made. Every public declaration below has a faithful full-telescope typed Reg attempt. The terminal elementary coercivity snapshot and completed D5 producers retain their attribution; no proof escapes or external target suppliers are introduced.")),
            Describe.Lean(
                DescribeId.Create("higherlayerinsertionregret-slope-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.slope_upper"),
                H("Uniform upper slope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural j>=2 and real u>=2, logarithmicSlope(j,u) <= 2*j. The original weighted-sum and logarithm estimate supplies log_drop_upper and ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope. The domain includes u=2 and j=2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerinsertionregret-log-drop-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.log_drop_upper"),
                H("Uniform logarithmic drop"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural j>=2 and real 2<=u<=v, log(beta(j,u)/beta(j,v)) <= 2*j*log(v/u). The upper-slope proof has the same full domain. This canonical supplier is consumed by insertion_regret and ActualHigherLayerQuantitativeBudgetRepair.moving_interval_marginals, with the original constants and endpoint ties."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerinsertionregret-insertion-regret"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.insertion_regret"),
                H("insertion regret"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source header: theorem insertion_regret {j p : ℕ} (hj : 2 ≤ j) (hp : p.Prime)     {u priceLambda κ : ℝ} (hu : 2 ≤ u) (hLambda : 0 < priceLambda) (hroot : beta j u = priceLambda)     (hκ : 0 ≤ κ) (hpu : u ≤ (p : ℝ)) (hup : (p : ℝ) ≤ u * (1 + κ)) :     0 ≤ priceLambda - goldenLayerMarginal p j ∧       priceLambda - goldenLayerMarginal p j ≤ 2 * j * κ * priceLambda"))),
                DescribeRole.Theorem)
        )));
}
