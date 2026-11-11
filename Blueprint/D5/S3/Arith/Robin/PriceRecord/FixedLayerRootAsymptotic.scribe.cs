using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedLayerRootAsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FixedLayerRootAsymptotic",
        H("UNCOMPILED_UNACCEPTED source components"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED / RegUNVALIDATED. All proof bodies are uncompiled candidates. No Lean/Scribe/Reg build, kernel/axiom closure, lawful enrollment, source binding, official/RH acceptance, novelty or consensus is asserted. Ordinary Pro reasoning is fallible input. The final uniform paid-prefix repair, its uniform original-price consumer, and the optional elementary-energy consumer remain unfinished. The finite components must not be presented as those final theorems. Existing owners are imported with exact unapplied consumed-helper patches. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.")),
            Describe.Lean(
                DescribeId.Create("fixedlayerrootasymptotic-fixed-layer-root-offset-tendsto"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto"),
                H("fixed layer root offset tendsto"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem fixed_layer_root_offset_tendsto {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => (j : ℝ) * log (cutoff j (referencePrice X)) - log X)       atTop (𝓝 (log (j : ℝ)))"))),
                DescribeRole.Theorem)
        )));
}
