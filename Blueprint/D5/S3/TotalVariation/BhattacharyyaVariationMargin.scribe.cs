using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BhattacharyyaVariationMarginDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/TotalVariation/BhattacharyyaVariationMargin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A certified total-variation lower margin gives an explicit upper bound on Bhattacharyya affinity.",
        H("Bhattacharyya from a Variation Margin"),
        Blocks(
            Paragraph(Text(
                "The frozen Bhattacharyya owner already proves TV squared is at most one "
                    + "minus affinity squared. This module only exposes the reverse-use "
                    + "adapter needed by robust testing; it introduces no new information "
                    + "inequality.")),
            Describe.Lean(
                DescribeId.Create("margin-affinity-ceiling"),
                DeclarationHandle.Create(Prefix + "bhattacharyya_le_sqrt_one_sub_margin_sq"),
                H("A TV margin bounds affinity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For probability data p and q, any nonnegative margin delta below TV(p,q) forces BC(p,q) to be at most sqrt(1-delta squared). The proof is a direct rearrangement of the frozen complementary-square inequality."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This adapter is generic and can be reused by any observation lane that "
                    + "certifies a total-variation margin before invoking finite-shot error "
                    + "bounds."))))));
}
