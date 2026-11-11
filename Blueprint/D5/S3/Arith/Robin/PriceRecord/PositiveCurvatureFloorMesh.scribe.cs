using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;
internal sealed class PositiveCurvatureFloorMeshDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "PositiveCurvatureFloorMesh", H("SOURCE ONLY candidate"),
        Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Full mathematical candidate bodies exist. No parser, build, Lean kernel, axiom closure, Scribe, lawful registration, variation, binding, official or RH acceptance is asserted. Ordinary Pro input is fallible. The exact original-record/arbitrary-original-price/energy endgoals belong to other owners.")),
            Describe.Lean(
                DescribeId.Create("actual-two-four-positive-curvature-floor-mesh"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh.positive_curvature_floor_mesh"),
                H("positive_curvature_floor_mesh"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem positive_curvature_floor_mesh {α δ Δ : ℝ}     (hα : 0 < α) (hδ : 0 < δ) (hδα : δ < α)     (hΔ : 4 * α ^ 2 / δ + 2 * α ≤ Δ) :     let N : ℤ := ⌊Δ / α⌋; let r := Δ - ((N : ℝ) - 1) * α; ∃ A B : ℕ,       (B : ℤ) = ⌊r / δ⌋ - 1 ∧       (A : ℤ) = N - 1 - 2 * B ∧       (A : ℤ) + 2 * B = N - 1 ∧       (A + B : ℝ) ≤ Δ / α ∧       δ ≤ Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) ∧       Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) < 2 * δ"))),
                DescribeRole.Theorem)
        )));
}
