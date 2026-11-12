using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class FixedGapGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial formal development of the exact Mertens range-two problem; the full theorem remains open.",
        H("FixedGapGrowth"), Blocks(
            Describe.Lean(DescribeId.Create("additive-defect-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.additive_defect_bounds"),
                H("additive_defect_bounds"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. The pending combinatorial concatenation theorem must supply the hypotheses for the actual profile counts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-gap-log-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.fixed_gap_log_bounds"),
                H("fixed_gap_log_bounds"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. The pending combinatorial concatenation theorem must supply the hypotheses for the actual profile counts."))), DescribeRole.Theorem))));
}
