using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class FixedGapGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Components consumed by the exact Mertens range-two probability theorem.",
        H("FixedGapGrowth"), Blocks(
            Paragraph(Text("Declarations without a displayed formula retain explicit statement-projection gaps. Their descriptions state the model and proof roles; they do not claim a rendered formula for an unsupported projection.")),
            Describe.Lean(DescribeId.Create("additive-defect-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.additive_defect_bounds"),
                H("additive_defect_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. GrowthTransfer applies these estimates to logarithms of the actual profile counts using the proved padded concatenation inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-gap-log-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.fixed_gap_log_bounds"),
                H("fixed_gap_log_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. GrowthTransfer applies these estimates to logarithms of the actual profile counts using the proved padded concatenation inequality."))), DescribeRole.Theorem))));
}
