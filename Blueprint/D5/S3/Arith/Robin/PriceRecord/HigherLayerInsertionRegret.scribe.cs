using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLayerInsertionRegretDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HigherLayerInsertionRegret",
        H("Source candidates awaiting native checks"),
        Blocks(
            Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Full source candidates only. No Lean, Scribe or Reg compiler/kernel check, lawful registration, source occurrence binding, official/RH acceptance, literature novelty or consensus claim. Every public declaration below has a faithful full-telescope typed Reg attempt. The terminal elementary coercivity snapshot and completed uncompiled producers retain their attribution; no proof escapes or external target suppliers are introduced.")),
            Describe.Lean(
                DescribeId.Create("higherlayerinsertionregret-insertion-regret"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.insertion_regret"),
                H("insertion regret"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source header: theorem insertion_regret {j p : ℕ} (hj : 2 ≤ j) (hp : p.Prime)     {u priceLambda κ : ℝ} (hu : 2 ≤ u) (hLambda : 0 < priceLambda) (hroot : beta j u = priceLambda)     (hκ : 0 ≤ κ) (hpu : u ≤ (p : ℝ)) (hup : (p : ℝ) ≤ u * (1 + κ)) :     0 ≤ priceLambda - goldenLayerMarginal p j ∧       priceLambda - goldenLayerMarginal p j ≤ 2 * j * κ * priceLambda"))),
                DescribeRole.Theorem)
        )));
}
