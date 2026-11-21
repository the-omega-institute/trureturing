using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasCycleCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit coefficients in normalized top integral cycles of the signed fair-bias complex.",
        H("Coefficients of the normalized signed cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("normalized-cycle-unit-coefficients"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/FairBiasCycleCoefficients.normalized_cycle_unit_coefficients"),
            H("Each oriented face has coefficient zero, one, or minus one"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a finite binary column family and an order on its signed labels. " +
                    "Take an integral cycle supported on the signed facets and select an " +
                    "augmented face. The coefficient at each full-restriction facet is one " +
                    "if it equals the selected face, and zero otherwise.")),
                Paragraph(Text(
                    "Call a member of a basis passive when a smaller element can replace it. " +
                    "At a basis with a nonpassive element, use the boundary equation on the " +
                    "ridge opposite the least such element. Its other cofaces come later " +
                    "and the exchange preserves passivity and makes the inserted element passive.")),
                Paragraph(Text(
                    "Work backwards through the facet order. At a nonzero coefficient all " +
                    "elements outside the selected facet are nonpassive. A missing element " +
                    "of the selected facet exceeds any lower bound strictly below every " +
                    "nonpassive element. At any nonzero later coface the removed element " +
                    "therefore lies outside the selected facet and the inserted element lies in it.")),
                Paragraph(Text(
                    "The fundamental circuit of each admissible inserted element lies in the " +
                    "common part of the current and selected bases together with the removed " +
                    "and inserted elements. After contraction of the common part, two such " +
                    "insertions would be parallel, contrary to their independence in the selected " +
                    "basis. Each ridge equation therefore gives zero or the sole later " +
                    "coefficient times an incidence sign."))),
            DescribeRole.Theorem))));
}
